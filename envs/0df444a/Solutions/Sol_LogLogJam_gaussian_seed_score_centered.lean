-- Prove2me | solution 1 for LogLogJam.gaussian_seed_score_centered
-- status  : ACCEPTED   (prove)
-- author  : @Senrui Chen
-- created : 2026-11-26T09:42:19.982424+00:00
-- url     : https://prove2.me/submissions/d1000b7e-2d60-490d-afef-80bd8563bf4d

import Theorems.Thm_DeepLearningTheory_wick_theorem
import Theorems.Thm_FunctionalInequalities_Analysis_fderiv_det_eq_det_mul_trace_readable
import Definitions.Def_LogLogJam_Obs
open Matrix LogLogJam MeasureTheory DeepLearningTheory
open scoped Matrix.Norms.Elementwise ENNReal ComplexOrder Kronecker
set_option maxHeartbeats 500000

private theorem pair2 : pairings 2 = {Equiv.swap 0 1} := by decide
private theorem wick2 {n : ℕ} (K : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) :
    (∑ σ ∈ pairings 2, ∏ a ∈ Finset.univ.filter (fun a : Fin 2 => a < σ a),
      K (![i,j] a) (![i,j] (σ a))) = K i j := by
  rw [pair2]
  simp [Finset.prod_filter, Fin.prod_univ_two, Equiv.swap_apply_def]

private def HM {n : ℕ} (K : Matrix (Fin n) (Fin n) ℝ) (f : (Fin n → ℝ) → ℝ) (v : ℝ) : Prop :=
  Integrable (fun z => gaussianDensity K z*f z) ∧ gaussExpect K f = v

private theorem HM.sum {n : ℕ} {K : Matrix (Fin n) (Fin n) ℝ} {ι : Type}
    [Fintype ι] {f : ι → (Fin n → ℝ) → ℝ} {v : ι → ℝ}
    (h : ∀ i, HM K (f i) (v i)) : HM K (fun z => ∑ i, f i z) (∑ i, v i) := by
  unfold HM gaussExpect
  simp only [Finset.mul_sum]
  exact ⟨integrable_finsetSum _ (fun i _ => (h i).1),
    (integral_finsetSum _ (fun i _ => (h i).1)).trans
      (Finset.sum_congr rfl (fun i _ => (h i).2))⟩

private theorem HM.mul {n : ℕ} {K : Matrix (Fin n) (Fin n) ℝ}
    {f : (Fin n → ℝ) → ℝ} {v : ℝ} (h : HM K f v) (c : ℝ) :
    HM K (fun z => c * f z) (c * v) := by
  unfold HM gaussExpect
  simp only [mul_left_comm (gaussianDensity K _) c]
  exact ⟨h.1.const_mul c, (integral_const_mul ..).trans (congrArg (c*·) h.2)⟩

private theorem HM.add {n : ℕ} {K : Matrix (Fin n) (Fin n) ℝ}
    {f g : (Fin n → ℝ) → ℝ} {v w : ℝ} (h : HM K f v) (hg : HM K g w) :
    HM K (fun z => f z + g z) (v+w) := by
  unfold HM gaussExpect
  simp only [mul_add]
  exact ⟨h.1.add hg.1, (integral_add h.1 hg.1).trans (congrArg₂ (·+·) h.2 hg.2)⟩


private theorem centered {n : ℕ} (K A : Matrix (Fin n) (Fin n) ℝ) (hK : K.PosDef) :
    let F := fun z => gaussianDensity K z * (z ⬝ᵥ (A *ᵥ z) - (A*K).trace)
    Integrable F ∧ (∫ z, F z) = 0 := by
  have I2 (i j : Fin n) : gaussExpect K (fun z => z i*z j) = K i j := by
    have h := wick_theorem K hK 1 (![i,j] : Fin 2 → Fin n)
    change gaussExpect K (fun z => ∏ a : Fin 2, z (![i,j] a)) = _ at h
    rw [wick2] at h
    simpa [Fin.prod_univ_two] using h
  have I0 : gaussExpect K (fun _ => 1) = 1 := by
    have h := wick_theorem K hK 0 (Fin.elim0 : Fin 0 → Fin n)
    have p0 : pairings 0 = {1} := by decide
    simpa only [Nat.mul_zero, p0, Finset.sum_singleton, Finset.univ_eq_empty,
      Finset.filter_empty, Finset.prod_empty] using h
  have h0 : HM K (fun _ => 1) 1 := by
    refine ⟨?_,I0⟩
    by_contra hn
    rw [gaussExpect,integral_undef hn] at I0
    norm_num at I0
  have gpos (z : Fin n → ℝ) : 0 ≤ gaussianDensity K z := by unfold gaussianDensity; positivity
  have hg : Measurable (gaussianDensity K) := by unfold gaussianDensity gaussQuadForm; fun_prop
  have sqI (i : Fin n) : Integrable (fun z => gaussianDensity K z * (z i*z i)) := by
    by_contra hn
    have h := I2 i i
    rw [gaussExpect, integral_undef hn] at h
    exact (hK.diag_pos (i := i)).ne h
  have h2 (i j : Fin n) : HM K (fun z => z i*z j) (K i j) := by
    refine ⟨?_, I2 i j⟩
    apply ((sqI i).add (sqI j)).mono' (by fun_prop)
    filter_upwards with z
    simp only [Real.norm_eq_abs,abs_mul,abs_of_nonneg (gpos z),Pi.add_apply]
    rw [← mul_add]
    apply mul_le_mul_of_nonneg_left _ (gpos z)
    nlinarith [sq_nonneg (|z i|-|z j|),sq_abs (z i),sq_abs (z j),sq_nonneg (z i),sq_nonneg (z j)]
  have ks (i j : Fin n) : K i j = K j i := by
    simpa [conjTranspose_eq_transpose_of_trivial] using hK.isHermitian.apply j i
  have q (z : Fin n → ℝ) : z ⬝ᵥ (A *ᵥ z) = ∑ i, ∑ j, A i j * (z i*z j) := by
    simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]; ac_rfl
  have tr : (A*K).trace = ∑ i, ∑ j, A i j*K i j := by
    simp only [trace, diag_apply,mul_apply]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [ks j i]
  have hm : HM K (fun z => z ⬝ᵥ (A *ᵥ z)) (A*K).trace := by
    simp_rw [q, tr]
    exact HM.sum fun i => HM.sum fun j => (h2 i j).mul (A i j)
  have hc := hm.add (h0.mul (-(A*K).trace))
  change HM K (fun z => z ⬝ᵥ (A *ᵥ z) - (A*K).trace) 0
  simpa only [mul_one, add_neg_cancel, sub_eq_add_neg] using hc

private theorem centeredQ (k : ℕ) (D H : Matrix (Q k) (Q k) ℝ) (hD : D.PosDef) :
    let F := fun y => outDens k D y * (y ⬝ᵥ ((D⁻¹ * H * D⁻¹) *ᵥ y) - (D⁻¹*H).trace / 2)
    Integrable F ∧ (∫ y, F y) = 0 := by
  let F := fun y => outDens k D y * (y ⬝ᵥ ((D⁻¹ * H * D⁻¹) *ᵥ y) - (D⁻¹*H).trace / 2)
  change Integrable F ∧ (∫ y, F y) = 0
  let e : Fin (2*k) ≃ Q k := finProdFinEquiv.symm
  let g := MeasurableEquiv.piCongrLeft (fun _ : Q k => ℝ) e
  let S := D.submatrix e e
  let M := (D⁻¹ * H * D⁻¹).submatrix e e
  let K := (1/2:ℝ) • S
  have hS : S.PosDef := hD.submatrix e.injective
  have hK : K.PosDef := hS.smul (by norm_num)
  have hg (z : Fin (2*k) → ℝ) : g z ∘ e = z := by
    funext j; exact MeasurableEquiv.piCongrLeft_apply_apply (β := fun _ : Q k => ℝ) e z j
  have hq (B : Matrix (Q k) (Q k) ℝ) (z : Fin (2*k) → ℝ) :
      g z ⬝ᵥ (B *ᵥ g z) = z ⬝ᵥ (B.submatrix e e *ᵥ z) := by
    have hv : z ∘ e.symm = g z := by
      funext j
      obtain ⟨i,rfl⟩ := e.surjective j
      simpa [Function.comp_def] using (congrFun (hg z) i).symm
    rw [← comp_equiv_dotProduct_comp_equiv (g z) (B *ᵥ g z) e, hg,
      submatrix_mulVec_equiv, hv]
  have hhalf : K⁻¹ = (2:ℝ) • S⁻¹ := by
    apply Matrix.inv_eq_right_inv
    dsimp [K]
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.mul_nonsing_inv _ ((isUnit_iff_isUnit_det _).mp hS.isUnit)]
    norm_num
  have hform (z : Fin (2*k) → ℝ) : gaussQuadForm K z = 2 * (z ⬝ᵥ (S⁻¹ *ᵥ z)) := by
    simp only [gaussQuadForm, hhalf, Matrix.smul_apply, smul_eq_mul, dotProduct,
      Matrix.mulVec, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  have hnorm : Real.sqrt ((2*Real.pi)^(2*k) * K.det) = Real.pi^k * Real.sqrt D.det := by
    dsimp [K, S]
    rw [Matrix.det_smul,Fintype.card_fin,det_submatrix_equiv_self,← mul_assoc, ← mul_pow]
    rw [show 2 * Real.pi * (1/2) = Real.pi by ring, Real.sqrt_mul (by positivity),
      mul_comm 2 k, pow_mul, Real.sqrt_sq (by positivity)]
  have hrho (z : Fin (2*k) → ℝ) : outDens k D (g z) = gaussianDensity K z := by
    simp only [outDens, hq, ← inv_submatrix_equiv, gaussianDensity, hnorm, hform]
    change Real.exp (-(z ⬝ᵥ (S⁻¹ *ᵥ z))) / _ = _ * Real.exp _
    ring_nf
  have hMK : M*K = (1/2:ℝ) • ((D⁻¹ * H).submatrix e e) := by
    dsimp [M,K,S]
    rw [Matrix.mul_smul, submatrix_mul_equiv, mul_assoc (D⁻¹ * H),
      Matrix.nonsing_inv_mul _ ((isUnit_iff_isUnit_det _).mp hD.isUnit), mul_one]
  have htr (A : Matrix (Q k) (Q k) ℝ) : (A.submatrix e e).trace = A.trace := by
    exact e.sum_comp (fun i => A i i)
  have htr1 : (M*K).trace = (D⁻¹*H).trace / 2 := by
    simp [hMK, trace_smul,htr]; ring
  have eqg : F ∘ g = fun z => gaussianDensity K z * (z ⬝ᵥ (M *ᵥ z) - (M*K).trace) := by
    funext z
    simp [F,Function.comp_def,hrho,hq,htr1,M]
  have mp := volume_measurePreserving_piCongrLeft (fun _ : Q k => ℝ) e
  obtain ⟨hi,hz⟩ := centered K M hK
  constructor
  · exact (mp.integrable_comp_emb g.measurableEmbedding).mp (eqg ▸ hi)
  · rw [← mp.integral_comp' F]
    change (∫ z, (F ∘ g) z) = 0
    rw [eqg]
    exact hz

open scoped Matrix.Norms.Operator in
private theorem curveInverse {ι : Type} [Fintype ι] [DecidableEq ι]
    (D : ℝ → Matrix ι ι ℝ) (H : Matrix ι ι ℝ) (θ : ℝ)
    (hu : IsUnit (D θ)) (hd : ∀ i j, HasDerivAt (fun t => D t i j) (H i j) θ) :
    ∀ i j, HasDerivAt (fun t => (D t)⁻¹ i j) ((-(D θ)⁻¹ * H * (D θ)⁻¹) i j) θ := by
  have h : HasDerivAt D H θ := hasDerivAt_pi.mpr (fun i => hasDerivAt_pi.mpr (hd i))
  have hi := hasFDerivAt_ringInverse (𝕜 := ℝ) hu.unit
  rw [hu.unit_spec] at hi
  have hi' := hi.comp_hasDerivAt θ h
  intro i j
  have hv := hasDerivAt_pi.mp (hasDerivAt_pi.mp hi' i) j
  simpa only [Function.comp_def, _root_.neg_apply, ContinuousLinearMap.mulLeftRight_apply,
    coe_units_inv, hu.unit_spec, nonsing_inv_eq_ringInverse, neg_mul] using hv

private theorem detDiff {ι : Type} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℝ) : DifferentiableAt ℝ Matrix.det M := by
  exact (FunctionalInequalities.Analysis.detML.hasFDerivAt M).differentiableAt

private theorem score_test (k : ℕ) (D : ℝ → Matrix (Q k) (Q k) ℝ)
    (H : Matrix (Q k) (Q k) ℝ) (θ : ℝ) (hD : ∀ t, (D t).PosDef)
    (hd : ∀ i j, HasDerivAt (fun t => D t i j) (H i j) θ)
    (y : Q k → ℝ) :
    HasDerivAt (fun t => Real.log (outDens k (D t) y))
      (y ⬝ᵥ (((D θ)⁻¹ * H * (D θ)⁻¹) *ᵥ y) - ((D θ)⁻¹ * H).trace / 2) θ := by
  have h : HasDerivAt D H θ := hasDerivAt_pi.mpr (fun i => hasDerivAt_pi.mpr (hd i))
  have hdet := (detDiff (D θ)).hasFDerivAt.comp_hasDerivAt θ h
  erw [FunctionalInequalities.Analysis.fderiv_det_eq_det_mul_trace_readable _ _
    ((isUnit_iff_isUnit_det _).mp (hD θ).isUnit)] at hdet
  have hlog := hdet.log (hD θ).det_pos.ne'
  have hinv := curveInverse D H θ (hD θ).isUnit hd
  have hq : HasDerivAt (fun t => y ⬝ᵥ ((D t)⁻¹ *ᵥ y))
      (y ⬝ᵥ ((-(D θ)⁻¹ * H * (D θ)⁻¹) *ᵥ y)) θ := by
    unfold dotProduct Matrix.mulVec
    apply HasDerivAt.fun_sum
    intro i _
    apply HasDerivAt.const_mul
    apply HasDerivAt.fun_sum
    intro j _
    exact (hinv i j).mul_const _
  have heq : (fun t => Real.log (outDens k (D t) y)) = fun t =>
      -(y ⬝ᵥ ((D t)⁻¹ *ᵥ y)) - (Real.log (Real.pi^k) + Real.log (D t).det / 2) := by
    funext t
    have hpos := (hD t).det_pos
    simp [outDens, Real.log_div, Real.log_mul, Real.log_sqrt hpos.le,
      (show Real.pi ^ k ≠ 0 by positivity), (show Real.sqrt (D t).det ≠ 0 by positivity)]
  rw [heq]
  have hL := hq.neg.sub ((hasDerivAt_const θ (Real.log (Real.pi^k))).add (hlog.div_const 2))
  have Hdet : (D θ).det ≠ 0 := (hD θ).det_pos.ne'
  apply hL.congr_deriv
  simp [Function.comp_def,neg_mul, Matrix.neg_mulVec,dotProduct_neg,Hdet]

private theorem real_seed_psd (k : ℕ) (W : Q k → Q k → ℝ) (hW : IsCov k (Matrix.of W)) : (Matrix.of W).PosSemidef := by
  apply posSemidef_iff_dotProduct_mulVec.mpr
  refine ⟨?_, ?_⟩
  · simpa [IsHermitian, conjTranspose_eq_transpose_of_trivial] using hW.1
  · intro v
    have h := (Complex.nonneg_iff.mp (hW.2.dotProduct_mulVec_nonneg (fun i => (v i : ℂ)))).1
    simpa [dotProduct, Matrix.mulVec, Complex.mul_re, Complex.mul_im, Complex.re_sum] using h

private theorem outcome_posDef (lam θ : ℝ) (hlam : 1 < lam) (k : ℕ)
    (W : Q k → Q k → ℝ) (hW : IsCov k (Matrix.of W)) :
    (VsqK lam θ k + Matrix.of W).PosDef := by
  have hrot : (rot θ).det = 1 := by
    simp [rot, det_fin_two, ← sq, Real.cos_sq_add_sin_sq]
  have hU : IsUnit (rot θ) := (isUnit_iff_isUnit_det _).mpr (by simp [hrot])
  have hdiag : (diagonal ![lam, lam⁻¹]).PosDef := by
    apply PosDef.diagonal
    intro i
    fin_cases i <;> simp <;> positivity
  have hV : (Vsq lam θ).PosDef := by
    have h := hdiag.mul_mul_conjTranspose_same (B := rot θ)
      (vecMul_injective_of_isUnit hU)
    have heq : diagonal ![lam, lam⁻¹] = !![lam,0;0,lam⁻¹] := by
      ext i j; fin_cases i <;> fin_cases j <;> simp
    simpa [Vsq, heq, conjTranspose_eq_transpose_of_trivial] using h
  apply PosDef.add_posSemidef (hV.kronecker (PosDef.one : (1 : Matrix (Fin k) (Fin k) ℝ).PosDef))
  exact real_seed_psd k W hW

private noncomputable def velocity (lam θ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  (lam-lam⁻¹) • (rot θ * !![0,1;1,0] * (rot θ)ᵀ)

private theorem velocity_deriv (lam θ : ℝ) (i j : Fin 2) :
    HasDerivAt (fun t => Vsq lam t i j) (velocity lam θ i j) θ := by
  fin_cases i <;> fin_cases j
  all_goals
    simp [Vsq, velocity, rot, vecMul, dotProduct, Fin.sum_univ_two]
    apply HasDerivAt.congr_deriv (f := _) (f' := deriv _ θ)
    · apply DifferentiableAt.hasDerivAt
      fun_prop
    · simp (disch := fun_prop) [deriv_fun_mul, deriv_fun_add]
      ring


theorem solution (lam θ : ℝ) (hlam : 1 < lam) (k : ℕ) (W : Q k → Q k → ℝ)
    (hW : IsCov k (Matrix.of W)) :
    let q := fun t y => outDens k (VsqK lam t k + Matrix.of W) y
    (∀ y, DifferentiableAt ℝ (fun t => q t y) θ) ∧
    Integrable (fun y => deriv (fun t => q t y) θ) ∧
      (∫ y, deriv (fun t => q t y) θ) = 0 := by
  let D (t : ℝ) := VsqK lam t k + Matrix.of W
  let H := velocity lam θ ⊗ₖ (1 : Matrix (Fin k) (Fin k) ℝ)
  have hD (t) : (D t).PosDef := outcome_posDef lam t hlam k W hW
  have hd (i j : Q k) : HasDerivAt (fun t => D t i j) (H i j) θ :=
    ((velocity_deriv lam θ i.1 j.1).mul_const ((1 : Matrix (Fin k) (Fin k) ℝ) i.2 j.2)).add_const _
  have pos t (y : Q k → ℝ) : 0 < outDens k (D t) y := by
    have h := (hD t).det_pos
    unfold outDens; positivity
  have hdy y := (score_test k D H θ hD hd y).exp
  simp only [Real.exp_log (pos _ _)] at hdy
  change (∀ y, DifferentiableAt ℝ (fun t => outDens k (D t) y) θ) ∧
    Integrable (fun y => deriv (fun t => outDens k (D t) y) θ) ∧
    (∫ y, deriv (fun t => outDens k (D t) y) θ) = 0
  refine ⟨fun y => (hdy y).differentiableAt, ?_⟩
  simp_rw [(hdy _).deriv]
  exact centeredQ k (D θ) H (hD θ)
