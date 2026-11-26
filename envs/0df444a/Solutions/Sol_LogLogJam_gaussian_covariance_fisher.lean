-- Prove2me | solution 1 for LogLogJam.gaussian_covariance_fisher
-- status  : ACCEPTED   (prove)
-- author  : @Senrui Chen
-- created : 2026-11-26T09:39:48.25233+00:00
-- url     : https://prove2.me/submissions/699bda10-e4d5-4f3e-b1de-c783d8263070

import Theorems.Thm_DeepLearningTheory_wick_theorem
import Theorems.Thm_FunctionalInequalities_Analysis_fderiv_det_eq_det_mul_trace_readable
import Definitions.Def_LogLogJam_Obs

open DeepLearningTheory Equiv
set_option maxRecDepth 12000
set_option maxHeartbeats 2000000
private theorem pair2 : pairings 2 = {Equiv.swap 0 1} := by decide
private theorem pair4 : pairings 4 =
    {Equiv.swap 0 1 * Equiv.swap 2 3,
     Equiv.swap 0 2 * Equiv.swap 1 3,
     Equiv.swap 0 3 * Equiv.swap 1 2} := by decide
private theorem wick2 {n : ℕ} (K : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) :
    (∑ σ ∈ pairings 2, ∏ a ∈ Finset.univ.filter (fun a : Fin 2 => a < σ a),
      K (![i,j] a) (![i,j] (σ a))) = K i j := by
  rw [pair2]
  simp [Finset.prod_filter, Fin.prod_univ_two, Equiv.swap_apply_def]
private theorem wick4 {n : ℕ} (K : Matrix (Fin n) (Fin n) ℝ) (i j l m : Fin n) :
    (∑ σ ∈ pairings 4, ∏ a ∈ Finset.univ.filter (fun a : Fin 4 => a < σ a),
      K (![i,j,l,m] a) (![i,j,l,m] (σ a))) = K i j*K l m + K i l*K j m + K i m*K j l := by
  rw [pair4]
  repeat rw [Finset.sum_insert (by decide)]
  rw [Finset.sum_singleton]
  have f1 : Finset.univ.filter (fun a : Fin 4 => a < (Equiv.swap 0 1 * Equiv.swap 2 3 : Equiv.Perm (Fin 4)) a) = {0,2} := by decide
  have f2 : Finset.univ.filter (fun a : Fin 4 => a < (Equiv.swap 0 2 * Equiv.swap 1 3 : Equiv.Perm (Fin 4)) a) = {0,1} := by decide
  have f3 : Finset.univ.filter (fun a : Fin 4 => a < (Equiv.swap 0 3 * Equiv.swap 1 2 : Equiv.Perm (Fin 4)) a) = {0,1} := by decide
  rw [f1,f2,f3]
  repeat rw [Finset.prod_insert (by decide)]
  simp only [Finset.prod_singleton,add_assoc]
  rfl

open DeepLearningTheory MeasureTheory Matrix

private theorem mixed_moments_integrable {n : ℕ} (K : Matrix (Fin n) (Fin n) ℝ)
    (hK : K.PosDef)
    (I2 : ∀ i j : Fin n, gaussExpect K (fun z => z i*z j) = K i j)
    (I4 : ∀ i j l m : Fin n, gaussExpect K (fun z => z i*z j*z l*z m) =
      K i j*K l m + K i l*K j m + K i m*K j l) :
    (∀ i j : Fin n, Integrable (fun z => gaussianDensity K z * (z i*z j))) ∧
    (∀ i j l m : Fin n, Integrable (fun z => gaussianDensity K z * (z i*z j*z l*z m))) := by
  have gpos (z : Fin n → ℝ) : 0 ≤ gaussianDensity K z := by unfold gaussianDensity; positivity
  have hg : Measurable (gaussianDensity K) := by unfold gaussianDensity gaussQuadForm; fun_prop
  have sqI (i : Fin n) : Integrable (fun z => gaussianDensity K z * (z i*z i)) := by
    by_contra hn
    have h := I2 i i
    rw [gaussExpect, integral_undef hn] at h
    exact (hK.diag_pos (i := i)).ne h
  have fI (i : Fin n) : Integrable (fun z => gaussianDensity K z * (z i*z i*z i*z i)) := by
    by_contra hn
    have h := I4 i i i i
    rw [gaussExpect, integral_undef hn] at h
    nlinarith [hK.diag_pos (i := i), sq_pos_of_pos (hK.diag_pos (i := i))]
  constructor
  · intro i j
    apply ((sqI i).add (sqI j)).mono' (by fun_prop)
    filter_upwards with z
    simp only [Real.norm_eq_abs,abs_mul,abs_of_nonneg (gpos z),Pi.add_apply]
    rw [← mul_add]
    apply mul_le_mul_of_nonneg_left _ (gpos z)
    nlinarith [sq_nonneg (|z i|-|z j|),sq_abs (z i),sq_abs (z j),sq_nonneg (z i),sq_nonneg (z j)]
  · intro i j l m
    apply ((((fI i).add (fI j)).add (fI l)).add (fI m)).mono' (by fun_prop)
    filter_upwards with z
    simp only [Real.norm_eq_abs,abs_mul,abs_of_nonneg (gpos z),Pi.add_apply]
    simp only [← mul_add]
    apply mul_le_mul_of_nonneg_left _ (gpos z)
    have hab (a b : ℝ) : 2*(|a| * |b|)^2 ≤ a^4+b^4 := by
      rw [mul_pow,sq_abs,sq_abs]
      nlinarith [sq_nonneg (a^2-b^2)]
    nlinarith [hab (z i) (z j),hab (z l) (z m),
      sq_nonneg (|z i| * |z j| - |z l| * |z m|),sq_nonneg ((z i)^2),sq_nonneg ((z j)^2),
      sq_nonneg ((z l)^2),sq_nonneg ((z m)^2)]

open Matrix DeepLearningTheory MeasureTheory
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

private theorem wick_to_variance {n : ℕ} (K A : Matrix (Fin n) (Fin n) ℝ) (hK : K.PosDef)
    (hA : Aᵀ = A)
    (h0 : HM K (fun _ => 1) 1)
    (h2 : ∀ i j, HM K (fun z => z i*z j) (K i j))
    (h4 : ∀ i j l m, HM K (fun z => z i*z j*z l*z m)
      (K i j * K l m + K i l * K j m + K i m * K j l)) :
    let F := fun z => gaussianDensity K z * (z ⬝ᵥ (A *ᵥ z) - (A*K).trace)^2
    Integrable F ∧ (∫ z, F z) = 2 * ((A*K)*(A*K)).trace := by
  have ks (i j : Fin n) : K i j = K j i := by
    simpa [conjTranspose_eq_transpose_of_trivial] using hK.isHermitian.apply j i
  have asy (i j : Fin n) : A i j = A j i := congrFun (congrFun hA j) i
  have q (z : Fin n → ℝ) : z ⬝ᵥ (A *ᵥ z) = ∑ i, ∑ j, A i j * (z i*z j) := by
    simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]; ac_rfl
  have tr : (A*K).trace = ∑ i, ∑ j, A i j*K i j := by
    simp only [trace, diag_apply,mul_apply]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [ks j i]
  have hm : HM K (fun z => z ⬝ᵥ (A *ᵥ z)) (A*K).trace := by
    simp_rw [q, tr]
    exact HM.sum fun i => HM.sum fun j => (h2 i j).mul (A i j)
  let C := fun i j l m : Fin n => A i j*A l m
  have hraw := HM.sum fun i => HM.sum fun j => HM.sum fun l => HM.sum fun m => (h4 i j l m).mul (C i j l m)
  have qs (z : Fin n → ℝ) : (z ⬝ᵥ (A *ᵥ z))^2 = ∑ i, ∑ j, ∑ l, ∑ m, C i j l m * (z i*z j*z l*z m) := by
    rw [q, sq]
    simp only [Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
      Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun m _ => ?_
    dsimp [C]
    ring
  have P : (A*K).trace^2 = ∑ i, ∑ j, ∑ l, ∑ m, C i j l m * (K i j * K l m) := by
    rw [tr,sq]
    simp only [Finset.sum_mul,Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
      Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun m _ => ?_
    dsimp [C]; ring
  have X : ((A*K)*(A*K)).trace = ∑ i, ∑ j, ∑ l, ∑ m,
        C i j l m * (K i m * K j l) := by
    simp only [trace,diag_apply,mul_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    conv_rhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [Finset.sum_mul]
    simp_rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun m _ => ?_
    dsimp [C]
    rw [ks m i]
    ring
  have Y : (∑ i, ∑ j, ∑ l, ∑ m, C i j l m * (K i l * K j m)) =
      ∑ i, ∑ j, ∑ l, ∑ m, C i j l m * (K i m*K j l) := by
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun m _ => ?_
    simp only [C,asy m l]
  have hsq : HM K (fun z => (z ⬝ᵥ (A *ᵥ z))^2)
      ((A*K).trace^2 + 2 * ((A*K)*(A*K)).trace) := by
    simp_rw [qs]
    convert hraw using 1
    simp only [mul_add,Finset.sum_add_distrib, ← P, Y, ← X]
    ring
  have h := (hsq.add (hm.mul (-2*(A*K).trace))).add (h0.mul ((A*K).trace^2))
  change HM K (fun z => (z ⬝ᵥ (A *ᵥ z) - (A*K).trace)^2) (2 * ((A*K)*(A*K)).trace)
  convert h using 1
  · funext z; ring
  · ring

open Matrix LogLogJam MeasureTheory DeepLearningTheory
open scoped ENNReal
set_option maxHeartbeats 500000

private theorem quad_transport (k : ℕ) (D H : Matrix (Q k) (Q k) ℝ) (hD : D.PosDef)
    (hH : Hᵀ = H)
    (mom : ∀ {n : ℕ} (K A : Matrix (Fin n) (Fin n) ℝ), K.PosDef → Aᵀ = A →
      let F := fun z => gaussianDensity K z * (z ⬝ᵥ (A *ᵥ z) - (A*K).trace)^2
      Integrable F ∧ (∫ z, F z) = 2 * ((A*K)*(A*K)).trace) :
    (∫⁻ y, ENNReal.ofReal (outDens k D y) *
      ENNReal.ofReal ((y ⬝ᵥ ((D⁻¹ * H * D⁻¹) *ᵥ y) - (D⁻¹*H).trace / 2)^2)) =
      ENNReal.ofReal (((D⁻¹*H)*(D⁻¹*H)).trace / 2) := by
  let e : Fin (2*k) ≃ Q k := finProdFinEquiv.symm
  let g := MeasurableEquiv.piCongrLeft (fun _ : Q k => ℝ) e
  let S := D.submatrix e e
  let M := (D⁻¹ * H * D⁻¹).submatrix e e
  let K := (1/2:ℝ) • S
  have hS : S.PosDef := hD.submatrix e.injective
  have hK : K.PosDef := hS.smul (by norm_num)
  have hDi : D⁻¹ᵀ = D⁻¹ := by
    simpa [conjTranspose_eq_transpose_of_trivial] using hD.isHermitian.inv.eq
  have hM : Mᵀ = M := by
    have h : (D⁻¹ * H * D⁻¹)ᵀ = D⁻¹ * H * D⁻¹ := by simp [hH, hDi,mul_assoc]
    exact congrArg (fun A : Matrix (Q k) (Q k) ℝ => A.submatrix e e) h
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
  have htr2 : 2 * ((M*K)*(M*K)).trace = ((D⁻¹*H)*(D⁻¹*H)).trace / 2 := by
    simp [hMK,Matrix.smul_mul,Matrix.mul_smul,trace_smul,htr]; ring
  obtain ⟨hI,hm⟩ := mom K M hK hM
  rw [← htr2, ← hm, ofReal_integral_eq_lintegral_ofReal hI]
  · rw [← (volume_measurePreserving_piCongrLeft (fun _ : Q k => ℝ) e).lintegral_comp_emb
      g.measurableEmbedding]
    apply lintegral_congr
    intro z
    change ENNReal.ofReal (outDens k D (g z)) * ENNReal.ofReal ((g z ⬝ᵥ _ - _)^2) = _
    rw [hrho, hq, htr1, ENNReal.ofReal_mul (by unfold gaussianDensity; positivity)]
  · filter_upwards with z
    unfold gaussianDensity
    positivity

open Matrix LogLogJam
open scoped Matrix.Norms.Elementwise
set_option maxHeartbeats 600000

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
    deriv (fun t => Real.log (outDens k (D t) y)) θ =
      y ⬝ᵥ (((D θ)⁻¹ * H * (D θ)⁻¹) *ᵥ y) - ((D θ)⁻¹ * H).trace / 2 := by
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
  have hf := hL.deriv
  change deriv (fun t => -(y ⬝ᵥ ((D t)⁻¹ *ᵥ y)) - (Real.log (Real.pi ^ k) + Real.log (D t).det / 2)) θ = _ at hf
  rw [hf]
  simp [Function.comp_def, neg_mul, Matrix.neg_mulVec, dotProduct_neg, Hdet]


private theorem gaussianQuadraticVariance {n : ℕ} (K A : Matrix (Fin n) (Fin n) ℝ)
    (hK : K.PosDef) (hA : Aᵀ = A) :
    let F := fun z => gaussianDensity K z * (z ⬝ᵥ (A *ᵥ z) - (A*K).trace)^2
    Integrable F ∧ (∫ z, F z) = 2 * ((A*K)*(A*K)).trace := by
  have I2 (i j : Fin n) : gaussExpect K (fun z => z i*z j) = K i j := by
    have h := wick_theorem K hK 1 (![i,j] : Fin 2 → Fin n)
    change gaussExpect K (fun z => ∏ a : Fin 2, z (![i,j] a)) = _ at h
    rw [wick2] at h
    simpa [Fin.prod_univ_two] using h
  have I4 (i j l m : Fin n) : gaussExpect K (fun z => z i*z j*z l*z m) =
      K i j * K l m + K i l * K j m + K i m * K j l := by
    have h := wick_theorem K hK 2 (![i,j,l,m] : Fin 4 → Fin n)
    change gaussExpect K (fun z => ∏ a : Fin 4, z (![i,j,l,m] a)) = _ at h
    rw [wick4] at h
    simpa [Fin.prod_univ_four,mul_assoc] using h
  have h0 : gaussExpect K (fun _ => 1) = 1 := by
    have h := wick_theorem K hK 0 (Fin.elim0 : Fin 0 → Fin n)
    have p0 : pairings 0 = {1} := by decide
    simpa only [Nat.mul_zero, p0, Finset.sum_singleton, Finset.univ_eq_empty,
      Finset.filter_empty, Finset.prod_empty] using h
  obtain ⟨a,b⟩ := mixed_moments_integrable K hK I2 I4
  apply wick_to_variance K A hK hA _ (fun i j => ⟨a i j,I2 i j⟩)
    (fun i j l m => ⟨b i j l m,I4 i j l m⟩)
  refine ⟨?_,h0⟩
  by_contra hn
  rw [gaussExpect, integral_undef hn] at h0
  norm_num at h0

theorem solution (k : ℕ) (D : ℝ → Matrix (Q k) (Q k) ℝ)
    (H : Matrix (Q k) (Q k) ℝ) (θ : ℝ) (hD : ∀ t, (D t).PosDef)
    (hd : ∀ i j, HasDerivAt (fun t => D t i j) (H i j) θ) :
    fisherInfo volume (fun t y => outDens k (D t) y) θ =
      ENNReal.ofReal (((((D θ)⁻¹ * H) * ((D θ)⁻¹ * H)).trace) / 2) := by
  have hsym : Hᵀ = H := by
    ext i j
    have hh : (fun t => D t j i) = fun t => D t i j := by
      funext t
      simpa [conjTranspose_eq_transpose_of_trivial] using (hD t).isHermitian.apply i j
    apply (hd j i).unique
    simpa [hh] using (hd i j)
  unfold fisherInfo
  simp_rw [score_test k D H θ hD hd]
  exact quad_transport k (D θ) H (hD θ) hsym gaussianQuadraticVariance
