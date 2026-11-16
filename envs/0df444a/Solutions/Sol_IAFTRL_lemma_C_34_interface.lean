-- Prove2me | solution 1 for IAFTRL.lemma_C_34_interface
-- status  : ACCEPTED   (prove)
-- author  : @Canzhe Zhao
-- created : 2026-11-15T11:57:03.326819+00:00
-- url     : https://prove2.me/submissions/b4801c10-c60f-4a34-8813-a9bc0054401c

import Mathlib
import Definitions.Def_IAFTRL_IsActionSet
import Definitions.Def_IAFTRL_IsIAFTRLRun
import Definitions.Def_LinearBanditProtocol
import Definitions.Def_IAFTRL_Zd
import Definitions.Def_IAFTRL_beta
import Definitions.Def_IAFTRL_Bc
import Definitions.Def_IAFTRL_Gam
import Definitions.Def_IAFTRL_qSoft
import Definitions.Def_IAFTRL_refArm
import Definitions.Def_IAFTRL_vCoef
import Definitions.Def_IAFTRL_IsFeasible2_3
import Definitions.Def_IAFTRL_IsMin2_3
import Definitions.Def_IAFTRL_Run_cumEst
import Definitions.Def_IAFTRL_Run_thetaHat

open Matrix IAFTRL MeasureTheory

namespace C34

variable {d K : ℕ}

/-! ### Linear algebra of the reconstruction -/

lemma gram_qf {K r : ℕ} (X : Fin K → Fin r → ℝ) (n : Fin K → ℝ) (v : Fin r → ℝ) :
    v ⬝ᵥ ((∑ c, n c • vecMulVec (X c) (X c)) *ᵥ v) = ∑ c, n c * (X c ⬝ᵥ v) ^ 2 := by
  rw [dotProduct_comm]
  simp only [Matrix.sum_mulVec, Matrix.smul_mulVec, vecMulVec_mulVec, sum_dotProduct,
    smul_dotProduct, smul_eq_mul, op_smul_eq_smul]
  exact Finset.sum_congr rfl fun c _ => by ring

lemma gram_herm {K r : ℕ} (X : Fin K → Fin r → ℝ) (n : Fin K → ℝ) :
    (∑ c, n c • vecMulVec (X c) (X c)).IsHermitian := by
  ext i j
  simp [Matrix.conjTranspose_apply, Matrix.sum_apply, vecMulVec_apply, mul_comm]

lemma eq_zero_of_orth (arms : Fin K → Fin d → ℝ)
    (hspan : Submodule.span ℝ (Set.range arms) = ⊤) (w : Fin d → ℝ)
    (h : ∀ c, arms c ⬝ᵥ w = 0) : w = 0 := by
  have : ∀ v ∈ Submodule.span ℝ (Set.range arms), v ⬝ᵥ w = 0 := by
    intro v hv
    induction hv using Submodule.span_induction with
    | mem x hx => obtain ⟨c, rfl⟩ := hx; exact h c
    | zero => simp
    | add x y _ _ hx hy => rw [add_dotProduct, hx, hy, add_zero]
    | smul t x _ hx => rw [smul_dotProduct, hx, smul_zero]
  have hw := this w (by rw [hspan]; trivial)
  exact dotProduct_self_eq_zero.mp hw

/-- a design with all weights positive on a spanning set is positive definite -/
lemma M_pd (arms : Fin K → Fin d → ℝ) (hspan : Submodule.span ℝ (Set.range arms) = ⊤)
    (p : Fin K → ℝ) (hp : ∀ b, 0 < p b) :
    (BanditAlgorithm.linearAllocationMatrix arms p).PosDef := by
  have hherm : (BanditAlgorithm.linearAllocationMatrix arms p).IsHermitian := by
    unfold BanditAlgorithm.linearAllocationMatrix; exact gram_herm arms p
  refine Matrix.PosDef.of_dotProduct_mulVec_pos hherm fun v hv => ?_
  rw [star_trivial]
  unfold BanditAlgorithm.linearAllocationMatrix
  rw [gram_qf]
  by_contra hle
  push Not at hle
  have hz : ∀ c, arms c ⬝ᵥ v = 0 := by
    intro c
    have hnn : ∀ b ∈ Finset.univ, 0 ≤ p b * (arms b ⬝ᵥ v) ^ 2 :=
      fun b _ => mul_nonneg (hp b).le (sq_nonneg _)
    have h0 : ∑ b, p b * (arms b ⬝ᵥ v) ^ 2 = 0 :=
      le_antisymm hle (Finset.sum_nonneg hnn)
    have := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp h0 c (Finset.mem_univ _)
    have h2 : (arms c ⬝ᵥ v) ^ 2 = 0 := by
      rcases mul_eq_zero.mp this with h | h
      · exact absurd h (hp c).ne'
      · exact h
    exact pow_eq_zero_iff (by norm_num) |>.mp h2
  exact hv (eq_zero_of_orth arms hspan v hz)

/-- difference unbiasedness of the reconstruction: `Σ_b p_b (x^⊤ v_b)(b^⊤ θ) = x^⊤ θ` -/
lemma unbiased (arms : Fin K → Fin d → ℝ) (p : Fin K → ℝ)
    (hM : (BanditAlgorithm.linearAllocationMatrix arms p).PosDef) (x θ : Fin d → ℝ) :
    ∑ b, x ⬝ᵥ vCoef arms p b * (arms b ⬝ᵥ θ) * p b = x ⬝ᵥ θ := by
  set M := BanditAlgorithm.linearAllocationMatrix arms p with hMdef
  have hdet : IsUnit M.det := (Matrix.isUnit_iff_isUnit_det M).mp hM.isUnit
  have hMθ : M *ᵥ θ = ∑ b, (p b * (arms b ⬝ᵥ θ)) • arms b := by
    simp only [M, BanditAlgorithm.linearAllocationMatrix, Matrix.sum_mulVec, Matrix.smul_mulVec,
      vecMulVec_mulVec, op_smul_eq_smul]
    exact Finset.sum_congr rfl fun b _ => by rw [smul_smul]
  have e : x ⬝ᵥ θ = x ⬝ᵥ (M⁻¹ *ᵥ (M *ᵥ θ)) := by
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hdet, Matrix.one_mulVec]
  rw [e, hMθ, Matrix.mulVec_sum, dotProduct_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  unfold vCoef
  rw [Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]
  ring

/-- the row-variance identity `Σ_b p_b (x^⊤ v_b)² = x^⊤ M^{-1} x` -/
lemma var_id (arms : Fin K → Fin d → ℝ) (p : Fin K → ℝ)
    (hM : (BanditAlgorithm.linearAllocationMatrix arms p).PosDef) (x : Fin d → ℝ) :
    ∑ b, p b * (x ⬝ᵥ vCoef arms p b) ^ 2 =
      x ⬝ᵥ (BanditAlgorithm.linearAllocationMatrix arms p)⁻¹ *ᵥ x := by
  set M := BanditAlgorithm.linearAllocationMatrix arms p with hMdef
  have hdet : IsUnit M.det := (Matrix.isUnit_iff_isUnit_det M).mp hM.isUnit
  have hMinvT : M⁻¹ᵀ = M⁻¹ := by
    rw [Matrix.transpose_nonsing_inv]
    congr 1
    have := hM.1
    rwa [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] at this
  set z := M⁻¹ *ᵥ x with hz
  have hrow : ∀ b, x ⬝ᵥ vCoef arms p b = arms b ⬝ᵥ z := by
    intro b
    unfold vCoef
    rw [hz, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, ← hMdef, hMinvT,
      dotProduct_comm]
  simp_rw [hrow]
  have hqf : z ⬝ᵥ M *ᵥ z = ∑ b, p b * (arms b ⬝ᵥ z) ^ 2 := by
    simp only [M]; unfold BanditAlgorithm.linearAllocationMatrix; exact gram_qf arms p z
  rw [← hqf, hz, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet, Matrix.one_mulVec,
    dotProduct_comm]

/-! ### The selected law is fully supported -/

lemma qSoft_pos (β : ℝ) (arms : Fin K → Fin d → ℝ) (S : Fin d → ℝ) (a : Fin K) :
    0 < qSoft β arms S a := by
  unfold qSoft
  exact div_pos (Real.exp_pos _) (Finset.sum_pos (fun b _ => Real.exp_pos _) ⟨a, Finset.mem_univ _⟩)

lemma beta_ge (hd : 1 ≤ d) (s : ℕ) : 16 * (d : ℝ) ≤ beta d K s := by
  unfold beta; have := Real.sqrt_nonneg ((d : ℝ) * s / (1 + Real.log K)); linarith

lemma p_pos (hd : 1 ≤ d) (arms : Fin K → Fin d → ℝ) (s : ℕ) (S : Fin d → ℝ) (p : Fin K → ℝ)
    (hp : IsFeasible2_3 arms s S p) (b : Fin K) : 0 < p b := by
  obtain ⟨-, -, ⟨w, hw0, hwΓ, hpw⟩, -⟩ := hp
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  have hβ := beta_ge (K := K) hd s
  have hΓ : Gam d K s ≤ 1 / 4 := by
    unfold Gam
    rw [div_le_iff₀ (by linarith)]; linarith
  have hpb : p b = (1 - ∑ c, w c) * qSoft (beta d K s) arms S b + w b := by rw [hpw]
  rw [hpb]
  have hq := qSoft_pos (beta d K s) arms S b
  have := hw0 b
  have h1 : 0 < 1 - ∑ c, w c := by linarith
  positivity

/-! ### Reference action and gaps -/

lemma refArm_min (arms : Fin K → Fin d → ℝ) (S : Fin d → ℝ) (j : Fin K) :
    ∃ j₀, refArm arms S = arms j₀ ∧ ∀ i, arms j₀ ⬝ᵥ S ≤ arms i ⬝ᵥ S := by
  classical
  obtain ⟨m, -, hm⟩ := Finset.exists_min_image Finset.univ (fun i => arms i ⬝ᵥ S)
    ⟨j, Finset.mem_univ _⟩
  have hne : (Finset.univ.filter fun j : Fin K => ∀ i, arms j ⬝ᵥ S ≤ arms i ⬝ᵥ S).Nonempty :=
    ⟨m, Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun i => hm i (Finset.mem_univ _)⟩⟩
  refine ⟨_, ?_, (Finset.mem_filter.mp (Finset.min'_mem _ hne)).2⟩
  unfold refArm
  rw [dif_pos hne]

lemma Zd_nonneg (arms : Fin K → Fin d → ℝ) (S : Fin d → ℝ) (b : Fin K) : 0 ≤ Zd arms S b := by
  obtain ⟨j₀, hr, hj₀⟩ := refArm_min arms S b
  unfold Zd; rw [hr]; linarith [hj₀ b]

/-- `|(a − a*)^⊤ v_b| ≤ 2β + (Z_a + Z_{a*})/B` from (2.3d) -/
lemma row_diff (arms : Fin K → Fin d → ℝ) (s : ℕ) (S : Fin d → ℝ) (p : Fin K → ℝ)
    (hp : IsFeasible2_3 arms s S p) (a jstar b : Fin K) :
    |(arms a - arms jstar) ⬝ᵥ vCoef arms p b| ≤
      2 * beta d K s + (Zd arms S a + Zd arms S jstar) / Bc K := by
  obtain ⟨-, -, -, hd3, -⟩ := hp
  have h1 := hd3 a b
  have h2 := hd3 jstar b
  have e : (arms a - arms jstar) ⬝ᵥ vCoef arms p b =
      (arms a - refArm arms S) ⬝ᵥ vCoef arms p b -
        (arms jstar - refArm arms S) ⬝ᵥ vCoef arms p b := by
    rw [← sub_dotProduct]; congr 1; abel
  rw [e]
  have := abs_sub ((arms a - refArm arms S) ⬝ᵥ vCoef arms p b)
    ((arms jstar - refArm arms S) ⬝ᵥ vCoef arms p b)
  have e2 : (Zd arms S a + Zd arms S jstar) / Bc K = Zd arms S a / Bc K + Zd arms S jstar / Bc K :=
    add_div _ _ _
  linarith

/-! ### A deterministic envelope for the reference gaps ((C.230)) -/

/-- `W_0 = 0`, `W_{s+1} = W_s + 2(β_{s+1} + W_s/B)` -/
noncomputable def Wb (d K : ℕ) : ℕ → ℝ
  | 0 => 0
  | s + 1 => Wb d K s + 2 * (beta d K (s + 1) + Wb d K s / Bc K)

lemma Bc_pos (hK : 1 ≤ K) : 0 < Bc K := by
  unfold Bc
  have h2K : (1 : ℝ) ≤ 2 * K := by
    have : (1 : ℝ) ≤ K := by exact_mod_cast hK
    linarith
  have hl := Real.log_nonneg h2K
  have hc := Int.le_ceil (256 + Real.log (2 * (K : ℝ)))
  have : (0 : ℝ) < (⌈256 + Real.log (2 * (K : ℝ))⌉ : ℝ) := by linarith
  positivity

/-- one step of the envelope: if every gap at `S` is at most `w` and the update `θ̂` has rows
`|(c − r)^⊤ θ̂| ≤ β + Z_c/B`, then every gap at `S + θ̂` is at most `w + 2(β + w/B)` -/
lemma gap_step (arms : Fin K → Fin d → ℝ) (S θh : Fin d → ℝ) (β B w : ℝ) (hB : 0 < B)
    (hw : ∀ c, Zd arms S c ≤ w)
    (hrow : ∀ c, |(arms c - refArm arms S) ⬝ᵥ θh| ≤ β + Zd arms S c / B) (b : Fin K) :
    Zd arms (S + θh) b ≤ w + 2 * (β + w / B) := by
  obtain ⟨j₁, hr1, -⟩ := refArm_min arms (S + θh) b
  obtain ⟨j₀, hr0, hj₀⟩ := refArm_min arms S b
  have hZ : ∀ c, Zd arms S c = (arms c - arms j₀) ⬝ᵥ S := fun c => by
    unfold Zd; rw [hr0, sub_dotProduct]
  have e : Zd arms (S + θh) b = (Zd arms S b - Zd arms S j₁) +
      ((arms b - refArm arms S) ⬝ᵥ θh - (arms j₁ - refArm arms S) ⬝ᵥ θh) := by
    rw [hZ, hZ]
    unfold Zd
    rw [hr1, hr0]
    simp only [dotProduct_add, sub_dotProduct]
    ring
  rw [e]
  have h1 := hw b
  have h2 := Zd_nonneg arms S j₁
  have h3 := hrow b
  have h4 := hrow j₁
  have h5 : Zd arms S b / B ≤ w / B := div_le_div_of_nonneg_right (hw b) hB.le
  have h6 : Zd arms S j₁ / B ≤ w / B := div_le_div_of_nonneg_right (hw j₁) hB.le
  have := abs_sub ((arms b - refArm arms S) ⬝ᵥ θh) ((arms j₁ - refArm arms S) ⬝ᵥ θh)
  have := le_abs_self ((arms b - refArm arms S) ⬝ᵥ θh - (arms j₁ - refArm arms S) ⬝ᵥ θh)
  linarith

/-- the reference gaps of a run are bounded by the deterministic envelope `W_t` -/
lemma gap_env {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (hK : 1 ≤ K)
    (arms : Fin K → Fin d → ℝ) (T : ℕ) (R : Run d K Ω) (hR : IsIAFTRLRun P arms T R) :
    ∀ t ≤ T, ∀ ω b, Zd arms (R.cumEst arms t ω) b ≤ Wb d K t := by
  intro t
  induction t with
  | zero =>
    intro _ ω b
    have hS : R.cumEst arms 0 ω = 0 := by simp [Run.cumEst]
    rw [hS]
    have : Zd arms 0 b = 0 := by unfold Zd; simp
    rw [this]; simp [Wb]
  | succ s ih =>
    intro hs ω b
    have ih' := ih (by omega) ω
    have hfe := ((hR s (by omega)).2.1.2 ω).1
    obtain ⟨-, -, -, hd3, -⟩ := hfe
    have hS : R.cumEst arms (s + 1) ω = R.cumEst arms s ω + R.thetaHat arms s ω := by
      simp [Run.cumEst, Finset.sum_range_succ]
    rw [hS]
    simp only [Wb]
    refine gap_step arms _ _ (beta d K (s + 1)) (Bc K) (Wb d K s) (Bc_pos hK) ih' (fun c => ?_) b
    unfold Run.thetaHat
    rw [dotProduct_smul, smul_eq_mul, abs_mul]
    have hY : |R.Y s ω| ≤ 1 := (hR s (by omega)).2.2.2.1.1 ω
    have h := hd3 c (R.A s ω)
    have h0 := abs_nonneg ((arms c - refArm arms (R.cumEst arms s ω)) ⬝ᵥ
      vCoef arms (R.p s ω) (R.A s ω))
    nlinarith [abs_nonneg (R.Y s ω)]

/-! ### Measurability -/

lemma meas_vCoef (arms : Fin K → Fin d → ℝ) (b : Fin K) :
    Measurable (fun p : Fin K → ℝ => vCoef arms p b) := by
  have hM : Continuous (fun p : Fin K → ℝ => BanditAlgorithm.linearAllocationMatrix arms p) := by
    unfold BanditAlgorithm.linearAllocationMatrix
    exact continuous_finsetSum _ fun j _ => (continuous_apply j).smul continuous_const
  have e : (fun p : Fin K → ℝ => vCoef arms p b) = fun p =>
      (BanditAlgorithm.linearAllocationMatrix arms p).det⁻¹ •
        ((BanditAlgorithm.linearAllocationMatrix arms p).adjugate *ᵥ arms b) := by
    funext p
    unfold vCoef
    rw [Matrix.inv_def, Ring.inverse_eq_inv', Matrix.smul_mulVec]
  rw [e]
  exact (hM.matrix_det.measurable.inv).smul
    ((hM.matrix_adjugate.matrix_mulVec continuous_const).measurable)

lemma meas_v {Ω : Type*} {m : MeasurableSpace Ω} (arms : Fin K → Fin d → ℝ)
    (p : Ω → Fin K → ℝ) (A : Ω → Fin K) (hp : Measurable[m] p) (hA : Measurable[m] A) :
    Measurable[m] (fun ω => vCoef arms (p ω) (A ω)) := by
  have h2 : Measurable (fun q : (Fin K → ℝ) × Fin K => vCoef arms q.1 q.2) :=
    measurable_from_prod_countable_left fun b => meas_vCoef arms b
  have hv := h2.comp (hp.prodMk hA)
  dsimp only [Function.comp_def] at hv
  exact hv

lemma meas_D {Ω : Type*} {m : MeasurableSpace Ω} (arms : Fin K → Fin d → ℝ) (x : Fin d → ℝ)
    (Y : Ω → ℝ) (p : Ω → Fin K → ℝ) (A : Ω → Fin K) (hY : Measurable[m] Y)
    (hp : Measurable[m] p) (hA : Measurable[m] A) :
    Measurable[m] (fun ω => x ⬝ᵥ (Y ω • vCoef arms (p ω) (A ω))) :=
  (continuous_const.dotProduct continuous_id).measurable.comp (hY.smul (meas_v arms p A hp hA))

end C34

namespace C34

variable {d K : ℕ}

lemma int_of_bdd {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P]
    (f : Ω → ℝ) (hf : Measurable f) (C : ℝ) (h : ∀ ω, |f ω| ≤ C) : Integrable f P :=
  Integrable.of_bound hf.aestronglyMeasurable C
    (Filter.Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact h ω)

lemma abs_dot_le (arms : Fin K → Fin d → ℝ) (θ : Fin d → ℝ) (j : Fin K) :
    |arms j ⬝ᵥ θ| ≤ IAFTRL.actionNorm arms θ :=
  le_ciSup (f := fun j => |arms j ⬝ᵥ θ|) (Set.finite_range _).bddAbove j

lemma ind_apply {Ω : Type*} (A : Ω → Fin K) (b : Fin K) (ω : Ω) :
    (A ⁻¹' {b}).indicator (fun _ => (1 : ℝ)) ω = if A ω = b then 1 else 0 := by
  by_cases h : A ω = b
  · rw [Set.indicator_of_mem (by simpa using h), if_pos h]
  · rw [Set.indicator_of_notMem (by simpa using h), if_neg h]

end C34

theorem solution {d K : ℕ} (hd : 1 ≤ d) (arms : Fin K → Fin d → ℝ)
    (hA : IsActionSet arms) (jstar : Fin K) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (T : ℕ) (R : Run d K Ω) (hR : IsIAFTRLRun P arms T R) :
    ∀ t < T, ∀ a : Fin K,
      (Measurable[R.G (t + 1)] (fun ω => (arms a - arms jstar) ⬝ᵥ R.thetaHat arms t ω) ∧
        Measurable (fun ω => (arms a - arms jstar) ⬝ᵥ R.thetaHat arms t ω)) ∧
      P[fun ω => (arms a - arms jstar) ⬝ᵥ R.thetaHat arms t ω | R.G t] =ᵐ[P]
        (fun ω => (arms a - arms jstar) ⬝ᵥ R.θs t ω) ∧
      (∀ ω, |(arms a - arms jstar) ⬝ᵥ R.thetaHat arms t ω| ≤ 2 * beta d K (t + 1) +
        (Zd arms (R.cumEst arms t ω) a + Zd arms (R.cumEst arms t ω) jstar) / Bc K) ∧
      P[fun ω => ((arms a - arms jstar) ⬝ᵥ R.thetaHat arms t ω) ^ 2 | R.G t] ≤ᵐ[P]
        (fun ω => 4 * beta d K (t + 1) + 2 * (Zd arms (R.cumEst arms t ω) a ^ 2 +
          Zd arms (R.cumEst arms t ω) jstar ^ 2) / (Bc K * ((t : ℝ) + 1))) := by
  classical
  intro t ht a
  have hK : 1 ≤ K := Nat.one_le_iff_ne_zero.mpr (fun h => (h ▸ jstar).elim0)
  obtain ⟨⟨hAm, hYm, -, hGle, hhG, hθG, hGG, hAG, hYG⟩, ⟨hpm, hmin⟩, hlaw, ⟨hYb, hYc⟩, hθn⟩ :=
    hR t ht
  have hpG : Measurable[R.G t] (R.p t) := hpm.mono hhG le_rfl
  have hp0 : Measurable (R.p t) := hpm.mono (hhG.trans hGle) le_rfl
  have hBpos : 0 < Bc K := C34.Bc_pos hK
  have hDform : ∀ ω, (arms a - arms jstar) ⬝ᵥ R.thetaHat arms t ω =
      R.Y t ω * (arms a - arms jstar) ⬝ᵥ vCoef arms (R.p t ω) (R.A t ω) := by
    intro ω; unfold Run.thetaHat; rw [dotProduct_smul, smul_eq_mul]
  -- (1) measurability
  have hmeas1 : Measurable[R.G (t + 1)]
      (fun ω => (arms a - arms jstar) ⬝ᵥ R.thetaHat arms t ω) := by
    unfold Run.thetaHat
    exact C34.meas_D arms _ _ _ _ hYG (hpm.mono (hhG.trans hGG) le_rfl) hAG
  have hmeas0 : Measurable (fun ω => (arms a - arms jstar) ⬝ᵥ R.thetaHat arms t ω) := by
    unfold Run.thetaHat
    exact C34.meas_D arms _ _ _ _ hYm hp0 hAm
  -- (3) magnitude
  have hmag : ∀ ω, |(arms a - arms jstar) ⬝ᵥ R.thetaHat arms t ω| ≤ 2 * beta d K (t + 1) +
      (Zd arms (R.cumEst arms t ω) a + Zd arms (R.cumEst arms t ω) jstar) / Bc K := by
    intro ω
    rw [hDform, abs_mul]
    have h := C34.row_diff arms (t + 1) _ _ (hmin ω).1 a jstar (R.A t ω)
    have hY := hYb ω
    have h0 := abs_nonneg ((arms a - arms jstar) ⬝ᵥ vCoef arms (R.p t ω) (R.A t ω))
    nlinarith [abs_nonneg (R.Y t ω)]
  -- deterministic envelope for the row coefficients
  have hW := C34.gap_env P hK arms T R hR t ht.le
  have hc_bound : ∀ ω b, |(arms a - arms jstar) ⬝ᵥ vCoef arms (R.p t ω) b| ≤
      2 * beta d K (t + 1) + 2 * C34.Wb d K t / Bc K := by
    intro ω b
    have h := C34.row_diff arms (t + 1) _ _ (hmin ω).1 a jstar b
    have h1 := hW ω a
    have h2 := hW ω jstar
    have : (Zd arms (R.cumEst arms t ω) a + Zd arms (R.cumEst arms t ω) jstar) / Bc K ≤
        2 * C34.Wb d K t / Bc K := div_le_div_of_nonneg_right (by linarith) hBpos.le
    linarith
  set Kc := 2 * beta d K (t + 1) + 2 * C34.Wb d K t / Bc K with hKc
  -- the pieces
  let c : Fin K → Ω → ℝ := fun b ω => (arms a - arms jstar) ⬝ᵥ vCoef arms (R.p t ω) b
  let ind : Fin K → Ω → ℝ := fun b => (R.A t ⁻¹' {b}).indicator (fun _ => (1 : ℝ))
  let φ : Fin K → Ω → ℝ := fun b ω => arms b ⬝ᵥ R.θs t ω
  have hcG : ∀ b, StronglyMeasurable[R.G t] (c b) := fun b =>
    ((continuous_const.dotProduct continuous_id).measurable.comp
      ((C34.meas_vCoef arms b).comp hpG)).stronglyMeasurable
  have hc0 : ∀ b, Measurable (c b) := fun b =>
    (continuous_const.dotProduct continuous_id).measurable.comp ((C34.meas_vCoef arms b).comp hp0)
  have hφG : ∀ b, StronglyMeasurable[R.G t] (φ b) := fun b =>
    ((continuous_const.dotProduct continuous_id).measurable.comp hθG).stronglyMeasurable
  have hφ0 : ∀ b, Measurable (φ b) := fun b =>
    (continuous_const.dotProduct continuous_id).measurable.comp (hθG.mono hGle le_rfl)
  have hφb : ∀ b ω, |φ b ω| ≤ 1 := fun b ω => (C34.abs_dot_le arms _ b).trans (hθn ω)
  have hindS : ∀ b, MeasurableSet (R.A t ⁻¹' {b}) := fun b => hAm (measurableSet_singleton b)
  have hind0 : ∀ b, Measurable (ind b) := fun b => measurable_const.indicator (hindS b)
  have hindb : ∀ b ω, |ind b ω| ≤ 1 := fun b ω => by
    simp only [ind, C34.ind_apply]; split_ifs <;> simp
  have hind_int : ∀ b, Integrable (ind b) P := fun b =>
    C34.int_of_bdd P _ (hind0 b) 1 (hindb b)
  have hY_int : Integrable (R.Y t) P := C34.int_of_bdd P _ hYm 1 hYb
  have hg_int : ∀ b, Integrable (ind b * R.Y t) P := fun b =>
    C34.int_of_bdd P _ ((hind0 b).mul hYm) 1 fun ω => by
      simp only [Pi.mul_apply, abs_mul]
      nlinarith [hindb b ω, hYb ω, abs_nonneg (ind b ω), abs_nonneg (R.Y t ω)]
  have hcg_int : ∀ b, Integrable (c b * (ind b * R.Y t)) P := fun b =>
    C34.int_of_bdd P _ ((hc0 b).mul ((hind0 b).mul hYm)) Kc fun ω => by
      simp only [Pi.mul_apply, abs_mul]
      have h1 := hc_bound ω b
      have h2 := hindb b ω
      have h3 := hYb ω
      have h4 : |ind b ω| * |R.Y t ω| ≤ 1 := by
        nlinarith [abs_nonneg (ind b ω), abs_nonneg (R.Y t ω)]
      nlinarith [abs_nonneg (c b ω), abs_nonneg (ind b ω) , abs_nonneg (R.Y t ω),
        mul_nonneg (abs_nonneg (ind b ω)) (abs_nonneg (R.Y t ω))]
  -- the σ-algebra after the draw
  have hGH : R.G t ≤ R.G t ⊔ MeasurableSpace.comap (R.A t) inferInstance := le_sup_left
  have hHle : R.G t ⊔ MeasurableSpace.comap (R.A t) inferInstance ≤ ‹MeasurableSpace Ω› :=
    sup_le hGle hAm.comap_le
  have hindH : ∀ b, StronglyMeasurable[R.G t ⊔ MeasurableSpace.comap (R.A t) inferInstance]
      (ind b) := fun b => by
    have hs : MeasurableSet[R.G t ⊔ MeasurableSpace.comap (R.A t) inferInstance]
        (R.A t ⁻¹' {b}) :=
      le_sup_right (a := R.G t) _ (MeasurableSpace.measurableSet_comap.mpr
        ⟨{b}, measurableSet_singleton b, rfl⟩)
    exact stronglyMeasurable_const.indicator hs
  -- E[1{A=b} Y | G_t] = (b^⊤θ_t) p_{t,b}
  have hgb : ∀ b, P[ind b * R.Y t | R.G t] =ᵐ[P] φ b * fun ω => R.p t ω b := by
    intro b
    have s1 : P[ind b * R.Y t | R.G t ⊔ MeasurableSpace.comap (R.A t) inferInstance] =ᵐ[P]
        ind b * φ b := by
      refine (condExp_mul_of_stronglyMeasurable_left (hindH b) (hg_int b) hY_int).trans ?_
      filter_upwards [hYc] with ω hω
      simp only [Pi.mul_apply, hω, ind, φ, C34.ind_apply]
      split_ifs with h
      · rw [h]
      · simp
    have s2 : P[ind b * R.Y t | R.G t] =ᵐ[P] P[ind b * φ b | R.G t] :=
      (condExp_condExp_of_le hGH hHle).symm.trans (condExp_congr_ae s1)
    have hφi : Integrable (φ b * ind b) P :=
      C34.int_of_bdd P _ ((hφ0 b).mul (hind0 b)) 1 fun ω => by
        simp only [Pi.mul_apply, abs_mul]
        nlinarith [hφb b ω, hindb b ω, abs_nonneg (φ b ω), abs_nonneg (ind b ω)]
    have s3 : P[ind b * φ b | R.G t] =ᵐ[P] φ b * fun ω => R.p t ω b := by
      rw [mul_comm]
      exact (condExp_mul_of_stronglyMeasurable_left (hφG b) hφi (hind_int b)).trans
        ((Filter.EventuallyEq.rfl).mul (hlaw b))
    exact s2.trans s3
  have hcgb : ∀ b, P[c b * (ind b * R.Y t) | R.G t] =ᵐ[P]
      c b * (φ b * fun ω => R.p t ω b) := fun b =>
    (condExp_mul_of_stronglyMeasurable_left (hcG b) (hcg_int b) (hg_int b)).trans
      ((Filter.EventuallyEq.rfl).mul (hgb b))
  -- D as a finite sum
  have hDsum : (fun ω => (arms a - arms jstar) ⬝ᵥ R.thetaHat arms t ω) =
      ∑ b, c b * (ind b * R.Y t) := by
    funext ω
    rw [Finset.sum_apply, hDform]
    rw [Finset.sum_eq_single (R.A t ω)]
    · simp [c, ind, C34.ind_apply]; ring
    · intro b _ hb
      simp [c, ind, C34.ind_apply, Ne.symm hb]
    · simp
  -- (2) conditional mean
  have hmean : P[fun ω => (arms a - arms jstar) ⬝ᵥ R.thetaHat arms t ω | R.G t] =ᵐ[P]
      (fun ω => (arms a - arms jstar) ⬝ᵥ R.θs t ω) := by
    rw [hDsum]
    refine (condExp_finsetSum (fun b _ => hcg_int b) _).trans ?_
    have hall : ∀ᵐ ω ∂P, ∀ b, P[c b * (ind b * R.Y t) | R.G t] ω =
        c b ω * (φ b ω * R.p t ω b) := ae_all_iff.mpr fun b => hcgb b
    filter_upwards [hall] with ω hω
    rw [Finset.sum_apply]
    simp only [hω]
    have hMpd := C34.M_pd arms hA.2.2 (R.p t ω)
      (C34.p_pos hd arms (t + 1) _ _ (hmin ω).1)
    rw [← C34.unbiased arms (R.p t ω) hMpd (arms a - arms jstar) (R.θs t ω)]
    exact Finset.sum_congr rfl fun b _ => by simp only [c, φ]; ring
  -- (4) second moment
  have hsec : P[fun ω => ((arms a - arms jstar) ⬝ᵥ R.thetaHat arms t ω) ^ 2 | R.G t] ≤ᵐ[P]
      (fun ω => 4 * beta d K (t + 1) + 2 * (Zd arms (R.cumEst arms t ω) a ^ 2 +
        Zd arms (R.cumEst arms t ω) jstar ^ 2) / (Bc K * ((t : ℝ) + 1))) := by
    have hc2G : ∀ b, StronglyMeasurable[R.G t] (fun ω => c b ω ^ 2) := fun b => (hcG b).pow 2
    have hc2i : ∀ b, Integrable ((fun ω => c b ω ^ 2) * ind b) P := fun b =>
      C34.int_of_bdd P _ (((hc0 b).pow_const 2).mul (hind0 b)) (Kc ^ 2) fun ω => by
        simp only [Pi.mul_apply, abs_mul]
        have h1 : |c b ω ^ 2| ≤ Kc ^ 2 := by
          rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hc_bound ω b) 2
        have h2 := hindb b ω
        nlinarith [abs_nonneg (c b ω ^ 2), abs_nonneg (ind b ω)]
    have hD2i : Integrable (fun ω => ((arms a - arms jstar) ⬝ᵥ R.thetaHat arms t ω) ^ 2) P :=
      C34.int_of_bdd P _ (hmeas0.pow_const 2) (Kc ^ 2) fun ω => by
        rw [hDform, abs_pow, abs_mul]
        have h1 := hc_bound ω (R.A t ω)
        have h2 := hYb ω
        have h3 : |R.Y t ω| * |(arms a - arms jstar) ⬝ᵥ vCoef arms (R.p t ω) (R.A t ω)| ≤ Kc := by
          nlinarith [abs_nonneg (R.Y t ω),
            abs_nonneg ((arms a - arms jstar) ⬝ᵥ vCoef arms (R.p t ω) (R.A t ω))]
        exact pow_le_pow_left₀ (by positivity) h3 2
    have hpt : (fun ω => ((arms a - arms jstar) ⬝ᵥ R.thetaHat arms t ω) ^ 2) ≤ᵐ[P]
        ∑ b, (fun ω => c b ω ^ 2) * ind b := Filter.Eventually.of_forall fun ω => by
      beta_reduce
      rw [Finset.sum_apply, hDform]
      rw [Finset.sum_eq_single (R.A t ω)]
      · simp only [Pi.mul_apply, ind, C34.ind_apply, if_pos rfl, c, ↓reduceIte, mul_one]
        have h2 := hYb ω
        have h3 : R.Y t ω ^ 2 ≤ 1 := by
          have := abs_le.mp h2; nlinarith
        rw [mul_pow]
        have h4 := mul_le_mul_of_nonneg_right h3
          (sq_nonneg ((arms a - arms jstar) ⬝ᵥ vCoef arms (R.p t ω) (R.A t ω)))
        linarith
      · intro b _ hb
        simp [ind, C34.ind_apply, Ne.symm hb]
      · simp
    have hmono := condExp_mono (m := R.G t) hD2i (integrable_finsetSum' _ fun b _ => hc2i b) hpt
    have hsum := condExp_finsetSum (μ := P) (s := Finset.univ) (fun b _ => hc2i b) (R.G t)
    have hpb : ∀ b, P[(fun ω => c b ω ^ 2) * ind b | R.G t] =ᵐ[P]
        (fun ω => c b ω ^ 2) * fun ω => R.p t ω b := fun b =>
      (condExp_mul_of_stronglyMeasurable_left (hc2G b) (hc2i b) (hind_int b)).trans
        ((Filter.EventuallyEq.rfl).mul (hlaw b))
    have hall : ∀ᵐ ω ∂P, ∀ b, P[(fun ω => c b ω ^ 2) * ind b | R.G t] ω =
        c b ω ^ 2 * R.p t ω b := ae_all_iff.mpr fun b => hpb b
    filter_upwards [hmono, hsum, hall] with ω h1 h2 h3
    refine h1.trans ?_
    rw [h2, Finset.sum_apply]
    simp only [h3]
    -- Σ_b p_b c_b² ≤ 2 Σ p_b u_b² + 2 Σ p_b w_b²
    have hfe := (hmin ω).1
    have hMpd := C34.M_pd arms hA.2.2 (R.p t ω) (C34.p_pos hd arms (t + 1) _ _ hfe)
    obtain ⟨hp0', -, -, -, he, -⟩ := hfe
    set S := R.cumEst arms t ω
    set r := refArm arms S
    have hsplit : ∀ b, c b ω ^ 2 * R.p t ω b ≤
        2 * (R.p t ω b * ((arms a - r) ⬝ᵥ vCoef arms (R.p t ω) b) ^ 2) +
          2 * (R.p t ω b * ((arms jstar - r) ⬝ᵥ vCoef arms (R.p t ω) b) ^ 2) := by
      intro b
      have e : c b ω = (arms a - r) ⬝ᵥ vCoef arms (R.p t ω) b -
          (arms jstar - r) ⬝ᵥ vCoef arms (R.p t ω) b := by
        simp only [c]; rw [← sub_dotProduct]; congr 1; abel
      rw [e]
      have hpb := hp0' b
      nlinarith [mul_nonneg hpb (sq_nonneg ((arms a - r) ⬝ᵥ vCoef arms (R.p t ω) b +
        (arms jstar - r) ⬝ᵥ vCoef arms (R.p t ω) b))]
    have hs1 := Finset.sum_le_sum fun b (_ : b ∈ Finset.univ) => hsplit b
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
      C34.var_id arms _ hMpd, C34.var_id arms _ hMpd] at hs1
    have he1 := he a
    have he2 := he jstar
    push_cast at he1 he2
    have e3 : 4 * beta d K (t + 1) + 2 * (Zd arms S a ^ 2 + Zd arms S jstar ^ 2) /
        (Bc K * ((t : ℝ) + 1)) = 2 * (beta d K (t + 1) + Zd arms S a ^ 2 / (Bc K * ((t : ℝ) + 1))) +
        2 * (beta d K (t + 1) + Zd arms S jstar ^ 2 / (Bc K * ((t : ℝ) + 1))) := by ring
    rw [e3]
    linarith
  exact ⟨⟨hmeas1, hmeas0⟩, hmean, hmag, hsec⟩
