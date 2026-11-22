-- Prove2me | solution 1 for NestedSA.NASA.proposition_1_b
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-22T19:39:25.996492+00:00
-- url     : https://prove2.me/submissions/8a662d17-072e-4e0f-a386-b0b66893a4e7

import Mathlib
import Definitions.Def_SpectralProjGrad_Shared_IsProjOnto
import Definitions.Def_NestedSA_NASA_Basic
import Definitions.Def_NestedSA_NASA_Model

open MeasureTheory ProbabilityTheory NestedSA.NASA
open scoped RealInnerProductSpace ENNReal

namespace NestedSAProp1bAux

/-! ### Deterministic geometry and calculus helpers -/

private lemma proj_variational {n : ℕ} {X : Set (EuclideanSpace ℝ (Fin n))}
    (hX_cvx : Convex ℝ X) {P : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (hP : SpectralProjGrad.Shared.IsProjOnto X P)
    (u y : EuclideanSpace ℝ (Fin n)) (hy : y ∈ X) :
    ⟪u - P u, y - P u⟫ ≤ 0 := by
  by_contra h
  push Not at h
  have hne : y - P u ≠ 0 := by
    intro h0
    rw [h0, inner_zero_right] at h
    exact lt_irrefl 0 h
  have hnorm_pos : 0 < ‖y - P u‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hne)
  set t : ℝ := min 1 (⟪u - P u, y - P u⟫ / ‖y - P u‖ ^ 2)
  have ht_pos : 0 < t := lt_min zero_lt_one (div_pos h hnorm_pos)
  have ht_le_one : t ≤ 1 := min_le_left _ _
  have ht_le_div : t ≤ ⟪u - P u, y - P u⟫ / ‖y - P u‖ ^ 2 := min_le_right _ _
  have hzt_mem : (1 - t) • P u + t • y ∈ X :=
    hX_cvx (hP u).1 hy (by linarith) ht_pos.le (by ring)
  have hmin := (hP u).2 _ hzt_mem
  have hsq : ‖u - P u‖ ^ 2 ≤ ‖u - ((1 - t) • P u + t • y)‖ ^ 2 :=
    sq_le_sq' (by linarith [norm_nonneg (u - P u), norm_nonneg (u - ((1 - t) • P u + t • y))]) hmin
  have hdiff : u - ((1 - t) • P u + t • y) = (u - P u) - t • (y - P u) := by
    module
  rw [hdiff] at hsq
  rw [norm_sub_sq_real (u - P u) (t • (y - P u)), inner_smul_right, norm_smul,
    Real.norm_of_nonneg ht_pos.le, mul_pow] at hsq
  have h1 : 2 * t * ⟪u - P u, y - P u⟫ ≤ t ^ 2 * ‖y - P u‖ ^ 2 := by linarith
  have h2 : 2 * ⟪u - P u, y - P u⟫ ≤ t * ‖y - P u‖ ^ 2 := by nlinarith
  have h3 : t * ‖y - P u‖ ^ 2 ≤ ⟪u - P u, y - P u⟫ := by
    have := (le_div_iff₀ hnorm_pos).mp ht_le_div
    linarith
  linarith

private lemma isProjOnto_lipschitz {n : ℕ} {X : Set (EuclideanSpace ℝ (Fin n))}
    (hX_cvx : Convex ℝ X) {P : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (hP : SpectralProjGrad.Shared.IsProjOnto X P) :
    LipschitzWith 1 P := by
  rw [lipschitzWith_iff_norm_sub_le]
  intro u v
  simp only [NNReal.coe_one, one_mul]
  have h1 : ⟪u - P u, P v - P u⟫ ≤ 0 := proj_variational hX_cvx hP u (P v) (hP v).1
  have h2 : ⟪v - P v, P u - P v⟫ ≤ 0 := proj_variational hX_cvx hP v (P u) (hP u).1
  have h2' : ⟪-(v - P v), P v - P u⟫ ≤ 0 := by
    have : P v - P u = -(P u - P v) := by abel
    rw [this, inner_neg_left, inner_neg_right, neg_neg]
    exact h2
  have hsum : ⟪(u - v) - (P u - P v), P v - P u⟫ ≤ 0 := by
    have : (u - v) - (P u - P v) = (u - P u) + -(v - P v) := by abel
    rw [this, inner_add_left]
    linarith
  have hexp : ⟪(u - v) - (P u - P v), P v - P u⟫ =
      -⟪u - v, P u - P v⟫ + ‖P u - P v‖ ^ 2 := by
    have hp : P v - P u = -(P u - P v) := by abel
    rw [inner_sub_left, hp, inner_neg_right, inner_neg_right, real_inner_self_eq_norm_sq]
    ring
  rw [hexp] at hsum
  have hcs : ⟪u - v, P u - P v⟫ ≤ ‖u - v‖ * ‖P u - P v‖ := real_inner_le_norm _ _
  have hsq : ‖P u - P v‖ ^ 2 ≤ ‖u - v‖ * ‖P u - P v‖ := by linarith
  by_cases h0 : ‖P u - P v‖ = 0
  · rw [h0]; exact norm_nonneg _
  · have hpos : 0 < ‖P u - P v‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm h0)
    nlinarith

private lemma norm_d_le {n : ℕ} {X : Set (EuclideanSpace ℝ (Fin n))}
    (hX_cvx : Convex ℝ X)
    {P : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (hP : SpectralProjGrad.Shared.IsProjOnto X P)
    {x z : EuclideanSpace ℝ (Fin n)} (hx : x ∈ X) {β : ℝ} (hβ : 0 < β) :
    ‖ybar P x z β - x‖ ≤ ‖z‖ / β := by
  set d := ybar P x z β - x
  have hvar := proj_variational hX_cvx hP (x - β⁻¹ • z) x hx
  have h1 : (x - β⁻¹ • z) - ybar P x z β = -(d + β⁻¹ • z) := by
    dsimp [d]; module
  have h2 : x - ybar P x z β = -d := by
    dsimp [d]; abel
  have h321 : ⟪z, d⟫ + β * ‖d‖ ^ 2 ≤ 0 := by
    rw [show P (x - β⁻¹ • z) = ybar P x z β from rfl, h1, h2, inner_neg_left, inner_neg_right,
      neg_neg, inner_add_left, real_inner_self_eq_norm_sq, inner_smul_left] at hvar
    simp only [conj_trivial] at hvar
    have hmul := mul_le_mul_of_nonneg_left hvar hβ.le
    rw [mul_zero, mul_add, ← mul_assoc, mul_inv_cancel₀ hβ.ne', one_mul] at hmul
    linarith
  have hcs : -⟪z, d⟫ ≤ ‖z‖ * ‖d‖ := by
    have := neg_le_abs ⟪z, d⟫
    exact this.trans (abs_real_inner_le_norm z d)
  have hle : β * ‖d‖ ^ 2 ≤ ‖z‖ * ‖d‖ := by linarith
  rw [le_div_iff₀ hβ]
  by_cases h0 : ‖d‖ = 0
  · rw [h0, zero_mul]; exact norm_nonneg _
  · have hpos : 0 < ‖d‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm h0)
    nlinarith

private lemma run_x_mem {n m : ℕ} {X : Set (EuclideanSpace ℝ (Fin n))}
    (hX_cvx : Convex ℝ X) {P : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (hP : SpectralProjGrad.Shared.IsProjOnto X P)
    {a b β : ℝ} {τ : ℕ → ℝ} {x0 z0 : EuclideanSpace ℝ (Fin n)} {u0 : EuclideanSpace ℝ (Fin m)}
    {x z : ℕ → EuclideanSpace ℝ (Fin n)} {u G s : ℕ → EuclideanSpace ℝ (Fin m)}
    {J : ℕ → (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m))}
    (hrun : IsRun X P a b β τ x0 z0 u0 x z u G s J)
    (hτ_one : ∀ k, τ k ≤ 1) :
    ∀ k, x k ∈ X := by
  intro k
  induction k with
  | zero => rw [hrun.init_x]; exact hrun.x0_mem
  | succ k ih =>
    rw [hrun.step_x]
    have hcomb : x k + τ k • (ybar P (x k) (z k) β - x k) =
        (1 - τ k) • x k + τ k • ybar P (x k) (z k) β := by module
    rw [hcomb]
    exact hX_cvx ih (hP _).1 (by linarith [hτ_one k]) (hrun.τ_pos k).le (by ring)

private lemma norm_convex_comb_sq {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (u v : E) {α : ℝ} (h0 : 0 ≤ α) (h1 : α ≤ 1) :
    ‖(1 - α) • u + α • v‖ ^ 2 ≤ (1 - α) * ‖u‖ ^ 2 + α * ‖v‖ ^ 2 := by
  have hexp : ‖(1 - α) • u + α • v‖ ^ 2 =
      (1 - α) * ‖u‖ ^ 2 + α * ‖v‖ ^ 2 - α * (1 - α) * ‖u - v‖ ^ 2 := by
    rw [norm_add_sq_real, norm_sub_sq_real, norm_smul, norm_smul,
      Real.norm_of_nonneg (by linarith), Real.norm_of_nonneg h0,
      inner_smul_left, inner_smul_right]
    simp only [conj_trivial]
    ring
  rw [hexp]
  have hnn : 0 ≤ α * (1 - α) * ‖u - v‖ ^ 2 := by positivity
  linarith

private lemma norm_sub_sq_le_two {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (u v : E) : ‖u - v‖ ^ 2 ≤ 2 * ‖u‖ ^ 2 + 2 * ‖v‖ ^ 2 := by
  have h1 := norm_sub_sq_real u v
  have h2 := norm_add_sq_real u v
  have h3 : 0 ≤ ‖u + v‖ ^ 2 := sq_nonneg _
  linarith

private lemma lipschitz_g {n m : ℕ}
    {f : EuclideanSpace ℝ (Fin m) → ℝ}
    {g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}
    {Lf Lg Ldf Ldg : ℝ} (hA2 : Assumption2 f g Lf Lg Ldf Ldg) :
    LipschitzWith (Real.toNNReal Lg) g :=
  LipschitzWith.of_dist_le_mul fun a b => by
    rw [dist_eq_norm, dist_eq_norm, Real.coe_toNNReal Lg hA2.Lg_nonneg]
    exact hA2.lip_g a b

private lemma norm_fderiv_g_le {n m : ℕ}
    {f : EuclideanSpace ℝ (Fin m) → ℝ}
    {g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}
    {Lf Lg Ldf Ldg : ℝ} (hA2 : Assumption2 f g Lf Lg Ldf Ldg)
    (x : EuclideanSpace ℝ (Fin n)) :
    ‖fderiv ℝ g x‖ ≤ Lg := by
  have h := norm_fderiv_le_of_lipschitz ℝ (lipschitz_g hA2) (x₀ := x)
  rwa [Real.coe_toNNReal Lg hA2.Lg_nonneg] at h

private lemma norm_gradient_f_le {n m : ℕ}
    {f : EuclideanSpace ℝ (Fin m) → ℝ}
    {g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}
    {Lf Lg Ldf Ldg : ℝ} (hA2 : Assumption2 f g Lf Lg Ldf Ldg)
    (u : EuclideanSpace ℝ (Fin m)) :
    ‖gradient f u‖ ≤ Lf := by
  have hlip : LipschitzWith (Real.toNNReal Lf) f :=
    LipschitzWith.of_dist_le_mul fun a b => by
      rw [Real.dist_eq, dist_eq_norm, Real.coe_toNNReal Lf hA2.Lf_nonneg]
      exact hA2.lip_f a b
  have hfd : ‖fderiv ℝ f u‖ ≤ Lf := by
    have h := norm_fderiv_le_of_lipschitz ℝ hlip (x₀ := u)
    rwa [Real.coe_toNNReal Lf hA2.Lf_nonneg] at h
  rw [gradient, LinearIsometryEquiv.norm_map]
  exact hfd

private lemma continuous_fderiv_g {n m : ℕ}
    {f : EuclideanSpace ℝ (Fin m) → ℝ}
    {g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}
    {Lf Lg Ldf Ldg : ℝ} (hA2 : Assumption2 f g Lf Lg Ldf Ldg) :
    Continuous (fderiv ℝ g) :=
  (LipschitzWith.of_dist_le_mul (K := Real.toNNReal Ldg) fun a b => by
    rw [dist_eq_norm, dist_eq_norm, Real.coe_toNNReal Ldg hA2.Ldg_nonneg]
    exact hA2.lip_fderivg a b).continuous

private lemma continuous_gradient_f {n m : ℕ}
    {f : EuclideanSpace ℝ (Fin m) → ℝ}
    {g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}
    {Lf Lg Ldf Ldg : ℝ} (hA2 : Assumption2 f g Lf Lg Ldf Ldg) :
    Continuous (gradient f) :=
  (LipschitzWith.of_dist_le_mul (K := Real.toNNReal Ldf) fun a b => by
    rw [dist_eq_norm, dist_eq_norm, Real.coe_toNNReal Ldf hA2.Ldf_nonneg]
    exact hA2.lip_gradf a b).continuous

private lemma continuous_g {n m : ℕ}
    {f : EuclideanSpace ℝ (Fin m) → ℝ}
    {g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}
    {Lf Lg Ldf Ldg : ℝ} (hA2 : Assumption2 f g Lf Lg Ldf Ldg) :
    Continuous g :=
  (lipschitz_g hA2).continuous

private lemma continuous_adjoint_apply {n m : ℕ} :
    Continuous (Function.uncurry
      (fun (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m))
           (v : EuclideanSpace ℝ (Fin m)) => (ContinuousLinearMap.adjoint A) v)) :=
  (ContinuousLinearMap.adjoint.continuous.comp continuous_fst).clm_apply continuous_snd

private lemma aestronglyMeasurable_comp₂ {Ω β γ δ : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [TopologicalSpace β] [TopologicalSpace γ] [TopologicalSpace δ]
    {Φ : β → γ → δ} (hΦ : Continuous (Function.uncurry Φ))
    {f : Ω → β} {g : Ω → γ} (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ) :
    AEStronglyMeasurable (fun ω => Φ (f ω) (g ω)) μ :=
  hΦ.comp_aestronglyMeasurable (hf.prodMk hg)

private lemma stronglyMeasurable_comp₂ {Ω β γ δ : Type*} {m : MeasurableSpace Ω}
    [TopologicalSpace β] [TopologicalSpace γ] [TopologicalSpace δ]
    {Φ : β → γ → δ} (hΦ : Continuous (Function.uncurry Φ))
    {f : Ω → β} {g : Ω → γ} (hf : StronglyMeasurable[m] f) (hg : StronglyMeasurable[m] g) :
    StronglyMeasurable[m] (fun ω => Φ (f ω) (g ω)) :=
  hΦ.comp_stronglyMeasurable (hf.prodMk hg)

/-! ### Measure theory and Lp helpers -/

private lemma integrable_norm_sq_of_memLp {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] {μ : Measure Ω} {f : Ω → E} (hf : MemLp f 2 μ) :
    Integrable (fun ω => ‖f ω‖ ^ 2) μ :=
  hf.norm.integrable_sq

private lemma integrable_norm_sq_of_lintegral_lt_top {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] {μ : Measure Ω} {f : Ω → E}
    (hf_meas : AEStronglyMeasurable f μ)
    (hfin : ∫⁻ y, ‖f y‖ₑ ^ 2 ∂μ < ∞) :
    Integrable (fun y => ‖f y‖ ^ 2) μ := by
  refine ⟨hf_meas.norm.pow 2, ?_⟩
  rw [HasFiniteIntegral]
  have : (fun y => ‖‖f y‖ ^ 2‖ₑ) = fun y => ‖f y‖ₑ ^ 2 := by
    ext y
    rw [Real.enorm_eq_ofReal (sq_nonneg _), ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
  rw [this]
  exact hfin

private lemma integral_norm_sq_le_of_lintegral_le {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] {μ : Measure Ω} {f : Ω → E} {C : ℝ} (hC : 0 ≤ C)
    (hf_sq_int : Integrable (fun y => ‖f y‖ ^ 2) μ)
    (hlint : ∫⁻ y, ‖f y‖ₑ ^ 2 ∂μ ≤ ENNReal.ofReal C) :
    ∫ y, ‖f y‖ ^ 2 ∂μ ≤ C := by
  rw [← ENNReal.ofReal_le_ofReal_iff hC,
    ofReal_integral_eq_lintegral_ofReal hf_sq_int
      (Filter.Eventually.of_forall fun _ => sq_nonneg _)]
  have : (fun y => ENNReal.ofReal (‖f y‖ ^ 2)) = fun y => ‖f y‖ₑ ^ 2 := by
    ext y
    rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
  rw [this]
  exact hlint

private lemma integrable_and_integral_rTerm_parts {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {c_d γ b τk a Letaβ : ℝ}
    {f_d f_G f_3 f_4 f_z : Ω → ℝ}
    (h1 : Integrable f_d μ) (h2 : Integrable f_G μ)
    (h3 : Integrable f_3 μ) (h4 : Integrable f_4 μ) (h5 : Integrable f_z μ)
    (hz3 : ∫ ω, f_3 ω ∂μ = 0) (hz4 : ∫ ω, f_4 ω ∂μ = 0) :
    Integrable (fun ω => τk ^ 2 / 2 * (c_d * f_d ω + γ * b ^ 2 * f_G ω) +
        τk * (γ * b * (1 - b * τk) * f_3 ω + a * f_4 ω) + Letaβ / 2 * f_z ω) μ ∧
    ∫ ω, (τk ^ 2 / 2 * (c_d * f_d ω + γ * b ^ 2 * f_G ω) +
        τk * (γ * b * (1 - b * τk) * f_3 ω + a * f_4 ω) + Letaβ / 2 * f_z ω) ∂μ =
      τk ^ 2 / 2 * (c_d * ∫ ω, f_d ω ∂μ + γ * b ^ 2 * ∫ ω, f_G ω ∂μ) +
        Letaβ / 2 * ∫ ω, f_z ω ∂μ := by
  have hi1 : Integrable (fun ω => c_d * f_d ω) μ := h1.const_mul c_d
  have hi2 : Integrable (fun ω => γ * b ^ 2 * f_G ω) μ := h2.const_mul (γ * b ^ 2)
  have hi3 : Integrable (fun ω => γ * b * (1 - b * τk) * f_3 ω) μ := h3.const_mul _
  have hi4 : Integrable (fun ω => a * f_4 ω) μ := h4.const_mul a
  have hi5 : Integrable (fun ω => Letaβ / 2 * f_z ω) μ := h5.const_mul (Letaβ / 2)
  have hi12 : Integrable (fun ω => τk ^ 2 / 2 * (c_d * f_d ω + γ * b ^ 2 * f_G ω)) μ :=
    (hi1.add hi2).const_mul (τk ^ 2 / 2)
  have hi34 : Integrable (fun ω => τk * (γ * b * (1 - b * τk) * f_3 ω + a * f_4 ω)) μ :=
    (hi3.add hi4).const_mul τk
  have hi1234 : Integrable (fun ω =>
      τk ^ 2 / 2 * (c_d * f_d ω + γ * b ^ 2 * f_G ω) +
      τk * (γ * b * (1 - b * τk) * f_3 ω + a * f_4 ω)) μ :=
    hi12.add hi34
  refine ⟨hi1234.add hi5, ?_⟩
  rw [integral_add hi1234 hi5, integral_add hi12 hi34,
    integral_const_mul, integral_const_mul, integral_const_mul,
    integral_add hi1 hi2, integral_add hi3 hi4,
    integral_const_mul, integral_const_mul, integral_const_mul, integral_const_mul,
    hz3, hz4]
  ring

private lemma memLp_two_of_integrable_norm_sq {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] {μ : Measure Ω} {f : Ω → E}
    (hf_meas : AEStronglyMeasurable f μ) (hf_int : Integrable (fun ω => ‖f ω‖ ^ 2) μ) :
    MemLp f 2 μ := by
  refine ⟨hf_meas, ?_⟩
  rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top (by norm_num) (by norm_num)]
  simp only [ENNReal.toReal_ofNat]
  have h : (fun ω => ‖f ω‖ₑ ^ (2 : ℝ)) = fun ω => ‖‖f ω‖ ^ 2‖ₑ := by
    ext ω
    rw [Real.enorm_eq_ofReal (sq_nonneg _), ENNReal.ofReal_pow (norm_nonneg _),
      ofReal_norm, ENNReal.rpow_two]
  rw [h]
  exact hf_int.2

private lemma integrable_inner_of_memLp {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] {μ : Measure Ω} {f g : Ω → E}
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    Integrable (fun ω => ⟪f ω, g ω⟫) μ := by
  have hmul : Integrable (fun ω => ‖f ω‖ * ‖g ω‖) μ :=
    hf.norm.integrable_mul hg.norm
  refine hmul.mono' (hf.1.inner hg.1) (Filter.Eventually.of_forall fun ω => ?_)
  exact norm_inner_le_norm (f ω) (g ω)

private lemma memLp_two_comp_lipschitz {Ω E F : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [NormedAddCommGroup F] {μ : Measure Ω} [IsFiniteMeasure μ]
    {φ : E → F} {C : NNReal} (hφ : LipschitzWith C φ) {f : Ω → E} (hf : MemLp f 2 μ) :
    MemLp (fun ω => φ (f ω)) 2 μ := by
  have hbound : MemLp (fun ω => ‖φ 0‖ + (C : ℝ) * ‖f ω‖) 2 μ :=
    (memLp_const ‖φ 0‖).add (hf.norm.const_mul (C : ℝ))
  refine hbound.mono' (hφ.continuous.comp_aestronglyMeasurable hf.1)
    (Filter.Eventually.of_forall fun ω => ?_)
  have h1 := lipschitzWith_iff_norm_sub_le.mp hφ (f ω) 0
  have h2 : ‖φ (f ω)‖ - ‖φ 0‖ ≤ ‖φ (f ω) - φ 0‖ := norm_sub_norm_le _ _
  simp only [sub_zero] at h1
  linarith

private lemma integral_inner_eq_zero_of_condExp_zero {Ω E : Type*} {m : MeasurableSpace Ω}
    [mΩ : MeasurableSpace Ω] [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {μ : Measure Ω} [IsFiniteMeasure μ] (hm : m ≤ mΩ)
    {A B : Ω → E} (hA_meas : StronglyMeasurable[m] A) (hA_lp : MemLp A 2 μ)
    (hB_lp : MemLp B 2 μ) (hB_ce : μ[B | m] =ᵐ[μ] 0) :
    ∫ ω, ⟪A ω, B ω⟫ ∂μ = 0 := by
  have hAB_int : Integrable (fun ω => ⟪A ω, B ω⟫) μ :=
    integrable_inner_of_memLp hA_lp hB_lp
  have hB_int : Integrable B μ := hB_lp.integrable one_le_two
  have hpull : μ[fun ω => (innerSL ℝ) (A ω) (B ω) | m] =ᵐ[μ]
      fun ω => (innerSL ℝ) (A ω) (μ[B | m] ω) :=
    condExp_bilin_of_stronglyMeasurable_left (innerSL ℝ) hA_meas hAB_int hB_int
  have hzero : μ[fun ω => ⟪A ω, B ω⟫ | m] =ᵐ[μ] 0 := by
    filter_upwards [hpull, hB_ce] with ω h1 h2
    change (μ[fun ω => (innerSL ℝ) (A ω) (B ω) | m]) ω = 0
    rw [h1, h2, Pi.zero_apply, map_zero]
  calc ∫ ω, ⟪A ω, B ω⟫ ∂μ
      = ∫ ω, μ[fun ω => ⟪A ω, B ω⟫ | m] ω ∂μ := (integral_condExp hm).symm
    _ = ∫ ω, (0 : ℝ) ∂μ := integral_congr_ae hzero
    _ = 0 := integral_zero _ _

/-! ### Conditional independence via condExpKernel -/

private lemma ae_indepFun_condExpKernel {Ω β γ : Type*} {m' : MeasurableSpace Ω}
    [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    (hm' : m' ≤ mΩ)
    [TopologicalSpace β] [SecondCountableTopology β] [MeasurableSpace β] [BorelSpace β]
    [TopologicalSpace γ] [SecondCountableTopology γ] [MeasurableSpace γ] [BorelSpace γ]
    {X : Ω → β} {Y : Ω → γ} (hX : AEMeasurable X μ) (hY : AEMeasurable Y μ)
    (hXY : CondIndepFun m' hm' X Y μ) :
    ∀ᵐ ω ∂(μ.trim hm'), IndepFun X Y (condExpKernel μ m' ω) := by
  let X' := hX.mk X
  let Y' := hY.mk Y
  have hX'_meas : Measurable X' := hX.measurable_mk
  have hY'_meas : Measurable Y' := hY.measurable_mk
  have hX_ae : ∀ᵐ ω ∂(μ.trim hm'), X =ᵐ[condExpKernel μ m' ω] X' := by
    refine Measure.ae_ae_of_ae_comp ?_
    rw [condExpKernel_comp_trim hm']
    exact hX.ae_eq_mk
  have hY_ae : ∀ᵐ ω ∂(μ.trim hm'), Y =ᵐ[condExpKernel μ m' ω] Y' := by
    refine Measure.ae_ae_of_ae_comp ?_
    rw [condExpKernel_comp_trim hm']
    exact hY.ae_eq_mk
  have hXY' : CondIndepFun m' hm' X' Y' μ :=
    Kernel.IndepFun.congr' hXY hX_ae hY_ae
  have hmap : (condExpKernel μ m').map (fun y => (X' y, Y' y))
      =ᵐ[μ.trim hm'] (condExpKernel μ m').map X' ×ₖ (condExpKernel μ m').map Y' :=
    (condIndepFun_iff_map_prod_eq_prod_map_map hX'_meas hY'_meas).mp hXY'
  filter_upwards [hmap, hX_ae, hY_ae] with ω hω hXω hYω
  have hprod : (condExpKernel μ m' ω).map (fun y => (X' y, Y' y)) =
      Measure.prod ((condExpKernel μ m' ω).map X') ((condExpKernel μ m' ω).map Y') := by
    rw [← Kernel.map_apply _ (hX'_meas.prodMk hY'_meas), hω, Kernel.prod_apply,
      Kernel.map_apply _ hX'_meas, Kernel.map_apply _ hY'_meas]
  have hind' : IndepFun X' Y' (condExpKernel μ m' ω) :=
    (indepFun_iff_map_prod_eq_prod_map_map hX'_meas.aemeasurable hY'_meas.aemeasurable).mpr hprod
  exact hind'.congr hXω.symm hYω.symm

private lemma condExpKernel_lintegral_norm_sq_le {Ω E : Type*} {m' : MeasurableSpace Ω}
    [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (hm' : m' ≤ mΩ)
    [NormedAddCommGroup E] [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E]
    {X : Ω → E} (hX : MemLp X 2 μ) {C : ℝ}
    (hce : μ[fun ω => ‖X ω‖ ^ 2 | m'] ≤ᵐ[μ] fun _ => C) :
    ∀ᵐ ω ∂(μ.trim hm'), ∫⁻ y, ‖X y‖ₑ ^ 2 ∂(condExpKernel μ m' ω) ≤ ENNReal.ofReal C := by
  let X' := hX.1.mk X
  have hX'_sm : StronglyMeasurable X' := hX.1.stronglyMeasurable_mk
  have hX'_ae : X =ᵐ[μ] X' := hX.1.ae_eq_mk
  have hX'_sq_int : Integrable (fun y => ‖X' y‖ ^ 2) μ := by
    refine (integrable_norm_sq_of_memLp hX).congr ?_
    filter_upwards [hX'_ae] with y hy
    simp [hy]
  have hX_ae_trim : ∀ᵐ ω ∂(μ.trim hm'), X =ᵐ[condExpKernel μ m' ω] X' := by
    refine Measure.ae_ae_of_ae_comp ?_
    rw [condExpKernel_comp_trim hm']
    exact hX'_ae
  have hfin : ∀ᵐ ω ∂(μ.trim hm'), ∫⁻ y, ‖X' y‖ₑ ^ 2 ∂(condExpKernel μ m' ω) < ∞ := by
    have hmeas : Measurable[m'] (fun ω => ∫⁻ y, ‖X' y‖ₑ ^ 2 ∂(condExpKernel μ m' ω)) :=
      Measurable.lintegral_kernel (by fun_prop)
    refine ae_lt_top hmeas ?_
    rw [← Measure.lintegral_bind (condExpKernel μ m').aemeasurable (by fun_prop)]
    change ∫⁻ y, ‖X' y‖ₑ ^ 2 ∂(condExpKernel μ m' ∘ₘ μ.trim hm') ≠ ∞
    rw [condExpKernel_comp_trim hm']
    have heq : (fun y => ‖X' y‖ₑ ^ 2) = fun y => ‖‖X' y‖ ^ 2‖ₑ := by
      ext y
      rw [Real.enorm_eq_ofReal (sq_nonneg _), ENNReal.ofReal_pow (norm_nonneg _),
        ofReal_norm]
    rw [heq]
    exact hX'_sq_int.2.ne
  have hce_trim : μ[fun y => ‖X' y‖ ^ 2 | m'] ≤ᵐ[μ.trim hm'] fun _ => C := by
    have hce' : μ[fun y => ‖X' y‖ ^ 2 | m'] ≤ᵐ[μ] fun _ => C :=
      (condExp_congr_ae (by filter_upwards [hX'_ae] with y hy; simp [hy])).symm.le.trans hce
    exact stronglyMeasurable_condExp.ae_le_trim_of_stronglyMeasurable hm'
      stronglyMeasurable_const hce'
  have hker := condExp_ae_eq_trim_integral_condExpKernel hm' hX'_sq_int
  filter_upwards [hX_ae_trim, hfin, hce_trim, hker] with ω hXω hfinω hceω hkerω
  have hl_eq : ∫⁻ y, ‖X y‖ₑ ^ 2 ∂(condExpKernel μ m' ω) =
      ∫⁻ y, ‖X' y‖ₑ ^ 2 ∂(condExpKernel μ m' ω) := by
    refine lintegral_congr_ae ?_
    filter_upwards [hXω] with y hy
    simp [hy]
  rw [hl_eq]
  have hofReal : (fun y => ‖X' y‖ₑ ^ 2) = fun y => ENNReal.ofReal (‖X' y‖ ^ 2) := by
    ext y
    rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
  rw [hofReal]
  have hintω : Integrable (fun y => ‖X' y‖ ^ 2) (condExpKernel μ m' ω) := by
    refine ⟨(hX'_sm.norm.pow 2).aestronglyMeasurable, ?_⟩
    rw [HasFiniteIntegral]
    have : (fun y => ‖‖X' y‖ ^ 2‖ₑ) = fun y => ‖X' y‖ₑ ^ 2 := by
      ext y
      rw [Real.enorm_eq_ofReal (sq_nonneg _), ENNReal.ofReal_pow (norm_nonneg _),
        ofReal_norm]
    rw [this]
    exact hfinω
  rw [← ofReal_integral_eq_lintegral_ofReal hintω (Filter.Eventually.of_forall fun _ => sq_nonneg _)]
  rw [← hkerω]
  exact ENNReal.ofReal_le_ofReal hceω

/-- The oracle product `w^{k+1} = (J^{k+1})ᵀ s^{k+1}` is in `L²(μ)` with `E‖w^{k+1}‖² ≤ σJ² σs²`. -/
private lemma oracle_prod_memLp_and_sq_le {n m : ℕ} {Ω : Type*} [mΩ : MeasurableSpace Ω]
    [StandardBorelSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ] {ℱ : Filtration ℕ mΩ}
    {f : EuclideanSpace ℝ (Fin m) → ℝ}
    {g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}
    {x z : ℕ → Ω → EuclideanSpace ℝ (Fin n)}
    {u G s : ℕ → Ω → EuclideanSpace ℝ (Fin m)}
    {J : ℕ → Ω → (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m))}
    {σG σJ σs : ℝ} (hA1 : Assumption1 μ ℱ f g x z u G s J σG σJ σs) (k : ℕ) :
    let w : Ω → EuclideanSpace ℝ (Fin n) :=
      fun ω => (ContinuousLinearMap.adjoint (J (k + 1) ω)) (s (k + 1) ω)
    MemLp w 2 μ ∧ ∫ ω, ‖w ω‖ ^ 2 ∂μ ≤ σJ ^ 2 * σs ^ 2 := by
  intro w
  have hw_meas : AEStronglyMeasurable w μ :=
    aestronglyMeasurable_comp₂ continuous_adjoint_apply (hA1.memLp_J k).1 (hA1.memLp_s k).1
  have hw_norm_le : ∀ ω, ‖w ω‖ ≤ ‖J (k + 1) ω‖ * ‖s (k + 1) ω‖ := by
    intro ω
    calc ‖w ω‖
        ≤ ‖ContinuousLinearMap.adjoint (J (k + 1) ω)‖ * ‖s (k + 1) ω‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ = ‖J (k + 1) ω‖ * ‖s (k + 1) ω‖ := by
          rw [LinearIsometryEquiv.norm_map]
  have hind_trim : ∀ᵐ ω ∂(μ.trim (ℱ.le k)),
      IndepFun (s (k + 1)) (J (k + 1)) (condExpKernel μ (ℱ k) ω) :=
    ae_indepFun_condExpKernel (ℱ.le k) (hA1.memLp_s k).1.aemeasurable
      (hA1.memLp_J k).1.aemeasurable (hA1.condIndep_sJ k)
  have hs_ker := condExpKernel_lintegral_norm_sq_le (ℱ.le k) (hA1.memLp_s k)
    (hA1.condExp_s_sq k)
  have hJ_ker := condExpKernel_lintegral_norm_sq_le (ℱ.le k) (hA1.memLp_J k)
    (hA1.condExp_J_sq k)
  let s' := (hA1.memLp_s k).1.mk (s (k + 1))
  let J' := (hA1.memLp_J k).1.mk (J (k + 1))
  have hs'_meas : Measurable s' := (hA1.memLp_s k).1.stronglyMeasurable_mk.measurable
  have hJ'_meas : Measurable J' := (hA1.memLp_J k).1.stronglyMeasurable_mk.measurable
  have hs'_ae : ∀ᵐ ω ∂(μ.trim (ℱ.le k)), s (k + 1) =ᵐ[condExpKernel μ (ℱ k) ω] s' := by
    refine Measure.ae_ae_of_ae_comp ?_
    rw [condExpKernel_comp_trim (ℱ.le k)]
    exact (hA1.memLp_s k).1.ae_eq_mk
  have hJ'_ae : ∀ᵐ ω ∂(μ.trim (ℱ.le k)), J (k + 1) =ᵐ[condExpKernel μ (ℱ k) ω] J' := by
    refine Measure.ae_ae_of_ae_comp ?_
    rw [condExpKernel_comp_trim (ℱ.le k)]
    exact (hA1.memLp_J k).1.ae_eq_mk
  have hlint_prod : ∫⁻ y, ‖J' y‖ₑ ^ 2 * ‖s' y‖ₑ ^ 2 ∂μ ≤ ENNReal.ofReal (σJ ^ 2 * σs ^ 2) := by
    have hJ'_sq_meas : Measurable (fun y => ‖J' y‖ₑ ^ 2) := hJ'_meas.enorm.pow_const 2
    have hs'_sq_meas : Measurable (fun y => ‖s' y‖ₑ ^ 2) := hs'_meas.enorm.pow_const 2
    have hmeas_prod : Measurable (fun y => ‖J' y‖ₑ ^ 2 * ‖s' y‖ₑ ^ 2) :=
      hJ'_sq_meas.mul hs'_sq_meas
    calc ∫⁻ y, ‖J' y‖ₑ ^ 2 * ‖s' y‖ₑ ^ 2 ∂μ
        = ∫⁻ y, ‖J' y‖ₑ ^ 2 * ‖s' y‖ₑ ^ 2 ∂(condExpKernel μ (ℱ k) ∘ₘ μ.trim (ℱ.le k)) := by
          rw [condExpKernel_comp_trim (ℱ.le k)]
      _ = ∫⁻ ω, (∫⁻ y, ‖J' y‖ₑ ^ 2 * ‖s' y‖ₑ ^ 2 ∂(condExpKernel μ (ℱ k) ω)) ∂(μ.trim (ℱ.le k)) :=
          Measure.lintegral_bind (condExpKernel μ (ℱ k)).aemeasurable hmeas_prod.aemeasurable
      _ ≤ ∫⁻ _ω, ENNReal.ofReal (σJ ^ 2 * σs ^ 2) ∂(μ.trim (ℱ.le k)) := by
          refine lintegral_mono_ae ?_
          filter_upwards [hind_trim, hs_ker, hJ_ker, hs'_ae, hJ'_ae] with ω hindω hsω hJω hs'ω hJ'ω
          have hind' : IndepFun J' s' (condExpKernel μ (ℱ k) ω) :=
            (hindω.congr hs'ω hJ'ω).symm
          have hind_sq : IndepFun (fun y => ‖J' y‖ₑ ^ 2) (fun y => ‖s' y‖ₑ ^ 2)
              (condExpKernel μ (ℱ k) ω) :=
            hind'.comp (measurable_enorm.pow_const 2) (measurable_enorm.pow_const 2)
          rw [lintegral_mul_eq_lintegral_mul_lintegral_of_indepFun''
            hJ'_sq_meas.aemeasurable hs'_sq_meas.aemeasurable hind_sq]
          have hJ_eq : ∫⁻ y, ‖J' y‖ₑ ^ 2 ∂(condExpKernel μ (ℱ k) ω) =
              ∫⁻ y, ‖J (k + 1) y‖ₑ ^ 2 ∂(condExpKernel μ (ℱ k) ω) := by
            refine lintegral_congr_ae ?_
            filter_upwards [hJ'ω] with y hy; simp [hy]
          have hs_eq : ∫⁻ y, ‖s' y‖ₑ ^ 2 ∂(condExpKernel μ (ℱ k) ω) =
              ∫⁻ y, ‖s (k + 1) y‖ₑ ^ 2 ∂(condExpKernel μ (ℱ k) ω) := by
            refine lintegral_congr_ae ?_
            filter_upwards [hs'ω] with y hy; simp [hy]
          rw [hJ_eq, hs_eq, ENNReal.ofReal_mul (sq_nonneg σJ)]
          exact mul_le_mul' hJω hsω
      _ = ENNReal.ofReal (σJ ^ 2 * σs ^ 2) := by
          rw [lintegral_const, trim_measurableSet_eq (ℱ.le k) MeasurableSet.univ,
            measure_univ, mul_one]
  have hlint_w : ∫⁻ y, ‖w y‖ₑ ^ 2 ∂μ ≤ ENNReal.ofReal (σJ ^ 2 * σs ^ 2) := by
    calc ∫⁻ y, ‖w y‖ₑ ^ 2 ∂μ
        ≤ ∫⁻ y, ‖J' y‖ₑ ^ 2 * ‖s' y‖ₑ ^ 2 ∂μ := by
          refine lintegral_mono_ae ?_
          filter_upwards [(hA1.memLp_J k).1.ae_eq_mk, (hA1.memLp_s k).1.ae_eq_mk] with y hJy hsy
          dsimp only [J', s']
          rw [← hJy, ← hsy, ← mul_pow]
          have h1 : ‖w y‖ₑ ≤ ‖J (k + 1) y‖ₑ * ‖s (k + 1) y‖ₑ := by
            rw [← ofReal_norm, ← ofReal_norm, ← ofReal_norm,
              ← ENNReal.ofReal_mul (norm_nonneg _)]
            exact ENNReal.ofReal_le_ofReal (hw_norm_le y)
          exact pow_le_pow_left' h1 2
      _ ≤ ENNReal.ofReal (σJ ^ 2 * σs ^ 2) := hlint_prod
  have hw_sq_int : Integrable (fun y => ‖w y‖ ^ 2) μ :=
    integrable_norm_sq_of_lintegral_lt_top hw_meas (lt_of_le_of_lt hlint_w ENNReal.ofReal_lt_top)
  have hw_lp : MemLp w 2 μ := memLp_two_of_integrable_norm_sq hw_meas hw_sq_int
  have hw_int_le : ∫ y, ‖w y‖ ^ 2 ∂μ ≤ σJ ^ 2 * σs ^ 2 :=
    integral_norm_sq_le_of_lintegral_le (mul_nonneg (sq_nonneg σJ) (sq_nonneg σs))
      hw_sq_int hlint_w
  exact ⟨hw_lp, hw_int_le⟩

/-- Conditional expectation of `w^{k+1} = (J^{k+1})ᵀ s^{k+1}` given `ℱ k`. -/
private lemma oracle_prod_condExp {n m : ℕ} {Ω : Type*} [mΩ : MeasurableSpace Ω]
    [StandardBorelSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ] {ℱ : Filtration ℕ mΩ}
    {f : EuclideanSpace ℝ (Fin m) → ℝ}
    {g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}
    {x z : ℕ → Ω → EuclideanSpace ℝ (Fin n)}
    {u G s : ℕ → Ω → EuclideanSpace ℝ (Fin m)}
    {J : ℕ → Ω → (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m))}
    {σG σJ σs : ℝ} (hA1 : Assumption1 μ ℱ f g x z u G s J σG σJ σs) (k : ℕ)
    (hw_lp : MemLp (fun ω => (ContinuousLinearMap.adjoint (J (k + 1) ω)) (s (k + 1) ω)) 2 μ) :
    μ[fun ω => (ContinuousLinearMap.adjoint (J (k + 1) ω)) (s (k + 1) ω) | ℱ k] =ᵐ[μ]
      fun ω => (ContinuousLinearMap.adjoint (fderiv ℝ g (x (k + 1) ω))) (gradient f (u k ω)) := by
  let B : (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m)) →L[ℝ]
      EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
    ContinuousLinearMap.adjoint.toContinuousLinearMap
  have hind_trim : ∀ᵐ ω ∂(μ.trim (ℱ.le k)),
      IndepFun (s (k + 1)) (J (k + 1)) (condExpKernel μ (ℱ k) ω) :=
    ae_indepFun_condExpKernel (ℱ.le k) (hA1.memLp_s k).1.aemeasurable
      (hA1.memLp_J k).1.aemeasurable (hA1.condIndep_sJ k)
  have hker_w := condExp_ae_eq_integral_condExpKernel (ℱ.le k) (hw_lp.integrable one_le_two)
  have hker_J := condExp_ae_eq_integral_condExpKernel (ℱ.le k)
    ((hA1.memLp_J k).integrable one_le_two)
  have hker_s := condExp_ae_eq_integral_condExpKernel (ℱ.le k)
    ((hA1.memLp_s k).integrable one_le_two)
  have hJ_int_ae := ((hA1.memLp_J k).integrable one_le_two).condExpKernel_ae (m := ℱ k)
  have hs_int_ae := ((hA1.memLp_s k).integrable one_le_two).condExpKernel_ae (m := ℱ k)
  have hind_μ : ∀ᵐ ω ∂μ, IndepFun (J (k + 1)) (s (k + 1)) (condExpKernel μ (ℱ k) ω) := by
    filter_upwards [ae_of_ae_trim (ℱ.le k) hind_trim] with ω hω using hω.symm
  filter_upwards [hker_w, hker_J, hker_s, hJ_int_ae, hs_int_ae, hind_μ,
    hA1.condExp_J k, hA1.condExp_s k] with ω hkw hkJ hks hJi hsi hindω hceJ hces
  rw [hkw]
  have hbilin := hindω.integral_bilin hJi hsi B
  change ∫ y, B (J (k + 1) y) (s (k + 1) y) ∂condExpKernel μ (ℱ k) ω =
    B (fderiv ℝ g (x (k + 1) ω)) (gradient f (u k ω))
  rw [hbilin, ← hkJ, ← hks, hceJ, hces]

/-- L² membership, measurability, and moment bounds for iterates `z`, `d`, `x`, `u` and increments `z^{k+1} - z^k`. -/
private lemma iterate_moment_bounds {n m : ℕ} {Ω : Type*} [mΩ : MeasurableSpace Ω]
    [StandardBorelSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ] {ℱ : Filtration ℕ mΩ}
    {X : Set (EuclideanSpace ℝ (Fin n))} (hX_cvx : Convex ℝ X)
    {P : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (hP : SpectralProjGrad.Shared.IsProjOnto X P)
    {f : EuclideanSpace ℝ (Fin m) → ℝ}
    {g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}
    {Lf Lg Ldf Ldg : ℝ} (hA2 : Assumption2 f g Lf Lg Ldf Ldg)
    {a b β : ℝ} {τ : ℕ → ℝ} {x0 z0 : EuclideanSpace ℝ (Fin n)} {u0 : EuclideanSpace ℝ (Fin m)}
    {x z : ℕ → Ω → EuclideanSpace ℝ (Fin n)} {u G s : ℕ → Ω → EuclideanSpace ℝ (Fin m)}
    {J : ℕ → Ω → (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m))}
    (hrun : IsStochRun X P a b β τ x0 z0 u0 x z u G s J)
    {σG σJ σs : ℝ} (hA1 : Assumption1 μ ℱ f g x z u G s J σG σJ σs)
    (ha_pos : 0 < a) (hβ_pos : 0 < β) (hτ_pos : ∀ k, 0 < τ k) (hτ_le : ∀ k, τ k ≤ 1 / a)
    (hτ_one : ∀ k, τ k ≤ 1) (hτ0 : τ 0 = 1 / a) :
    (∀ k, StronglyMeasurable[ℱ k] (fun ω => ybar P (x k ω) (z k ω) β - x k ω)) ∧
    (∀ k, MemLp (fun ω => ybar P (x k ω) (z k ω) β - x k ω) 2 μ) ∧
    (∀ k, ∫ ω, ‖ybar P (x k ω) (z k ω) β - x k ω‖ ^ 2 ∂μ ≤
        max (σJ ^ 2 * σs ^ 2) (‖z0‖ ^ 2) / β ^ 2) ∧
    (∀ k, StronglyMeasurable[ℱ k] (x (k + 1))) ∧
    (∀ k, MemLp (fun ω => g (x (k + 1) ω)) 2 μ) ∧
    (∀ k, MemLp (u k) 2 μ) ∧
    (∀ k, Integrable (fun ω => ‖z (k + 1) ω - z k ω‖ ^ 2) μ) ∧
    (∀ N : ℕ, ∑ k ∈ Finset.range N, ∫ ω, ‖z (k + 1) ω - z k ω‖ ^ 2 ∂μ ≤
        2 * (‖z0‖ ^ 2 + 24 * a ^ 2 * σJ ^ 2 * σs ^ 2 * ∑ k ∈ Finset.range N, τ k ^ 2)) := by
  have haτ_pos : ∀ k, 0 < a * τ k := fun k => mul_pos ha_pos (hτ_pos k)
  have haτ_le_one : ∀ k, a * τ k ≤ 1 := fun k => by
    have := mul_le_mul_of_nonneg_left (hτ_le k) ha_pos.le
    rwa [mul_one_div_cancel ha_pos.ne'] at this
  have haτ0 : a * τ 0 = 1 := by rw [hτ0, mul_one_div_cancel ha_pos.ne']
  have hP_cont : Continuous P := (isProjOnto_lipschitz hX_cvx hP).continuous
  let w : ℕ → Ω → EuclideanSpace ℝ (Fin n) :=
    fun k ω => (ContinuousLinearMap.adjoint (J (k + 1) ω)) (s (k + 1) ω)
  let d : ℕ → Ω → EuclideanSpace ℝ (Fin n) :=
    fun k ω => ybar P (x k ω) (z k ω) β - x k ω
  have hw_props := fun k => oracle_prod_memLp_and_sq_le hA1 k
  have hw_lp : ∀ k, MemLp (w k) 2 μ := fun k => (hw_props k).1
  have hw_sq_le : ∀ k, ∫ ω, ‖w k ω‖ ^ 2 ∂μ ≤ σJ ^ 2 * σs ^ 2 := fun k => (hw_props k).2
  have hz_lp : ∀ k, MemLp (z k) 2 μ := by
    intro k
    induction k with
    | zero =>
      have : z 0 = fun _ => z0 := funext fun ω => (hrun ω).init_z
      rw [this]; exact memLp_const z0
    | succ k ih =>
      have hstep : z (k + 1) = fun ω => (1 - a * τ k) • z k ω + (a * τ k) • w k ω :=
        funext fun ω => (hrun ω).step_z k
      rw [hstep]
      exact (ih.const_smul (1 - a * τ k)).add ((hw_lp k).const_smul (a * τ k))
  have hz1_eq : z 1 = w 0 := by
    funext ω
    have hstep := (hrun ω).step_z 0
    simpa [w, haτ0] using hstep
  have hz_sq_le_pos : ∀ k, 1 ≤ k → ∫ ω, ‖z k ω‖ ^ 2 ∂μ ≤ σJ ^ 2 * σs ^ 2 := by
    intro k hk
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le' hk
    clear hk
    induction j with
    | zero =>
      simp only [zero_add, hz1_eq]
      exact hw_sq_le 0
    | succ j ih =>
      set k := j + 1
      have hstep : ∀ ω, ‖z (k + 1) ω‖ ^ 2 ≤
          (1 - a * τ k) * ‖z k ω‖ ^ 2 + (a * τ k) * ‖w k ω‖ ^ 2 := fun ω => by
        rw [(hrun ω).step_z k]
        exact norm_convex_comb_sq (z k ω) (w k ω) (haτ_pos k).le (haτ_le_one k)
      have hint_lhs : Integrable (fun ω => ‖z (k + 1) ω‖ ^ 2) μ :=
        integrable_norm_sq_of_memLp (hz_lp (k + 1))
      have hint_rhs : Integrable (fun ω => (1 - a * τ k) * ‖z k ω‖ ^ 2 +
          (a * τ k) * ‖w k ω‖ ^ 2) μ :=
        ((integrable_norm_sq_of_memLp (hz_lp k)).const_mul _).add
          ((integrable_norm_sq_of_memLp (hw_lp k)).const_mul _)
      calc ∫ ω, ‖z (k + 1) ω‖ ^ 2 ∂μ
          ≤ ∫ ω, ((1 - a * τ k) * ‖z k ω‖ ^ 2 + (a * τ k) * ‖w k ω‖ ^ 2) ∂μ :=
            integral_mono hint_lhs hint_rhs hstep
        _ = (1 - a * τ k) * ∫ ω, ‖z k ω‖ ^ 2 ∂μ + (a * τ k) * ∫ ω, ‖w k ω‖ ^ 2 ∂μ := by
            rw [integral_add ((integrable_norm_sq_of_memLp (hz_lp k)).const_mul _)
              ((integrable_norm_sq_of_memLp (hw_lp k)).const_mul _),
              integral_const_mul, integral_const_mul]
        _ ≤ (1 - a * τ k) * (σJ ^ 2 * σs ^ 2) + (a * τ k) * (σJ ^ 2 * σs ^ 2) := by
            have h1 : 0 ≤ 1 - a * τ k := by linarith [haτ_le_one k]
            have h2 : 0 ≤ a * τ k := (haτ_pos k).le
            nlinarith [ih, hw_sq_le k]
        _ = σJ ^ 2 * σs ^ 2 := by ring
  have hz_sq_le_max : ∀ k, ∫ ω, ‖z k ω‖ ^ 2 ∂μ ≤ max (σJ ^ 2 * σs ^ 2) (‖z0‖ ^ 2) := by
    intro k
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · have : (fun ω => ‖z 0 ω‖ ^ 2) = fun _ => ‖z0‖ ^ 2 :=
        funext fun ω => by rw [(hrun ω).init_z]
      rw [this, integral_const]
      simp
    · exact (hz_sq_le_pos k hk).trans (le_max_left _ _)
  have hd_sm : ∀ k, StronglyMeasurable[ℱ k] (d k) := by
    intro k
    have hx := hA1.adapted_x k
    have hz := hA1.adapted_z k
    have hybar : StronglyMeasurable[ℱ k] (fun ω => ybar P (x k ω) (z k ω) β) :=
      hP_cont.comp_stronglyMeasurable (hx.sub (hz.const_smul β⁻¹))
    exact hybar.sub hx
  have hx_mem : ∀ k ω, x k ω ∈ X := fun k ω => run_x_mem hX_cvx hP (hrun ω) hτ_one k
  have hd_norm_le : ∀ k ω, ‖d k ω‖ ≤ ‖z k ω‖ / β :=
    fun k ω => norm_d_le hX_cvx hP (hx_mem k ω) hβ_pos
  have hd_lp : ∀ k, MemLp (d k) 2 μ := by
    intro k
    refine ((hz_lp k).norm.const_mul β⁻¹).mono' ((hd_sm k).mono (ℱ.le k)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => ?_)
    rw [inv_mul_eq_div]
    exact hd_norm_le k ω
  have hd_sq_le : ∀ k, ∫ ω, ‖d k ω‖ ^ 2 ∂μ ≤ max (σJ ^ 2 * σs ^ 2) (‖z0‖ ^ 2) / β ^ 2 := by
    intro k
    have hpt : ∀ ω, ‖d k ω‖ ^ 2 ≤ (β ^ 2)⁻¹ * ‖z k ω‖ ^ 2 := fun ω => by
      have h1 := hd_norm_le k ω
      have h2 : ‖d k ω‖ ^ 2 ≤ (‖z k ω‖ / β) ^ 2 :=
        sq_le_sq' (by linarith [norm_nonneg (d k ω), div_nonneg (norm_nonneg (z k ω)) hβ_pos.le]) h1
      rw [div_pow, div_eq_inv_mul] at h2
      exact h2
    calc ∫ ω, ‖d k ω‖ ^ 2 ∂μ
        ≤ ∫ ω, (β ^ 2)⁻¹ * ‖z k ω‖ ^ 2 ∂μ :=
          integral_mono (integrable_norm_sq_of_memLp (hd_lp k))
            ((integrable_norm_sq_of_memLp (hz_lp k)).const_mul _) hpt
      _ = (β ^ 2)⁻¹ * ∫ ω, ‖z k ω‖ ^ 2 ∂μ := integral_const_mul _ _
      _ ≤ (β ^ 2)⁻¹ * max (σJ ^ 2 * σs ^ 2) (‖z0‖ ^ 2) :=
          mul_le_mul_of_nonneg_left (hz_sq_le_max k) (inv_nonneg.mpr (sq_nonneg β))
      _ = max (σJ ^ 2 * σs ^ 2) (‖z0‖ ^ 2) / β ^ 2 := by rw [div_eq_inv_mul]
  have hx_succ_sm : ∀ k, StronglyMeasurable[ℱ k] (x (k + 1)) := by
    intro k
    have hstep : x (k + 1) = fun ω => x k ω + τ k • d k ω :=
      funext fun ω => (hrun ω).step_x k
    rw [hstep]
    exact (hA1.adapted_x k).add ((hd_sm k).const_smul (τ k))
  have hx_lp : ∀ k, MemLp (x k) 2 μ := by
    intro k
    induction k with
    | zero =>
      have : x 0 = fun _ => x0 := funext fun ω => (hrun ω).init_x
      rw [this]; exact memLp_const x0
    | succ k ih =>
      have hstep : x (k + 1) = fun ω => x k ω + τ k • d k ω :=
        funext fun ω => (hrun ω).step_x k
      rw [hstep]
      exact ih.add ((hd_lp k).const_smul (τ k))
  have hgx_lp : ∀ k, MemLp (fun ω => g (x (k + 1) ω)) 2 μ :=
    fun k => memLp_two_comp_lipschitz (lipschitz_g hA2) (hx_lp (k + 1))
  have hu_lp : ∀ k, MemLp (u k) 2 μ := by
    intro k
    induction k with
    | zero =>
      have : u 0 = fun _ => u0 := funext fun ω => (hrun ω).init_u
      rw [this]; exact memLp_const u0
    | succ k ih =>
      have hstep : u (k + 1) = fun ω => (1 - b * τ k) • u k ω + (b * τ k) • G (k + 1) ω :=
        funext fun ω => (hrun ω).step_u k
      rw [hstep]
      exact (ih.const_smul (1 - b * τ k)).add ((hA1.memLp_G k).const_smul (b * τ k))
  have hz_diff_int : ∀ k, Integrable (fun ω => ‖z (k + 1) ω - z k ω‖ ^ 2) μ :=
    fun k => integrable_norm_sq_of_memLp ((hz_lp (k + 1)).sub (hz_lp k))
  have hz_diff_0 : ∫ ω, ‖z 1 ω - z 0 ω‖ ^ 2 ∂μ ≤
      2 * ‖z0‖ ^ 2 + 48 * a ^ 2 * σJ ^ 2 * σs ^ 2 * τ 0 ^ 2 := by
    have hpt : ∀ ω, ‖z 1 ω - z 0 ω‖ ^ 2 ≤ 2 * ‖w 0 ω‖ ^ 2 + 2 * ‖z0‖ ^ 2 := fun ω => by
      have hz1 : z 1 ω = w 0 ω := congrFun hz1_eq ω
      rw [hz1, (hrun ω).init_z]
      exact norm_sub_sq_le_two (w 0 ω) z0
    have hint_rhs : Integrable (fun ω => 2 * ‖w 0 ω‖ ^ 2 + 2 * ‖z0‖ ^ 2) μ :=
      ((integrable_norm_sq_of_memLp (hw_lp 0)).const_mul 2).add (integrable_const _)
    have h1 : ∫ ω, ‖z 1 ω - z 0 ω‖ ^ 2 ∂μ ≤ 2 * (σJ ^ 2 * σs ^ 2) + 2 * ‖z0‖ ^ 2 := by
      calc ∫ ω, ‖z 1 ω - z 0 ω‖ ^ 2 ∂μ
          ≤ ∫ ω, (2 * ‖w 0 ω‖ ^ 2 + 2 * ‖z0‖ ^ 2) ∂μ :=
            integral_mono (hz_diff_int 0) hint_rhs hpt
        _ = 2 * ∫ ω, ‖w 0 ω‖ ^ 2 ∂μ + 2 * ‖z0‖ ^ 2 := by
            rw [integral_add ((integrable_norm_sq_of_memLp (hw_lp 0)).const_mul 2)
              (integrable_const _), integral_const_mul, integral_const]
            simp
        _ ≤ 2 * (σJ ^ 2 * σs ^ 2) + 2 * ‖z0‖ ^ 2 := by linarith [hw_sq_le 0]
    have ha2τ0 : a ^ 2 * τ 0 ^ 2 = 1 := by
      have := congrArg (· ^ 2) haτ0
      linarith [mul_pow a (τ 0) 2]
    have hnn : 0 ≤ σJ ^ 2 * σs ^ 2 := by positivity
    calc ∫ ω, ‖z 1 ω - z 0 ω‖ ^ 2 ∂μ
        ≤ 2 * (σJ ^ 2 * σs ^ 2) + 2 * ‖z0‖ ^ 2 := h1
      _ ≤ 2 * ‖z0‖ ^ 2 + 48 * (σJ ^ 2 * σs ^ 2) := by linarith
      _ = 2 * ‖z0‖ ^ 2 + 48 * (a ^ 2 * τ 0 ^ 2) * (σJ ^ 2 * σs ^ 2) := by rw [ha2τ0, mul_one]
      _ = 2 * ‖z0‖ ^ 2 + 48 * a ^ 2 * σJ ^ 2 * σs ^ 2 * τ 0 ^ 2 := by ring
  have hz_diff_pos : ∀ k, 1 ≤ k →
      ∫ ω, ‖z (k + 1) ω - z k ω‖ ^ 2 ∂μ ≤ 48 * a ^ 2 * σJ ^ 2 * σs ^ 2 * τ k ^ 2 := by
    intro k hk
    have hpt : ∀ ω, ‖z (k + 1) ω - z k ω‖ ^ 2 ≤
        (2 * (a * τ k) ^ 2) * ‖w k ω‖ ^ 2 + (2 * (a * τ k) ^ 2) * ‖z k ω‖ ^ 2 := fun ω => by
      have hsub : z (k + 1) ω - z k ω = (a * τ k) • (w k ω - z k ω) := by
        rw [(hrun ω).step_z k]
        module
      rw [hsub, norm_smul, Real.norm_of_nonneg (haτ_pos k).le, mul_pow]
      have h2 := norm_sub_sq_le_two (w k ω) (z k ω)
      have hsq : 0 ≤ (a * τ k) ^ 2 := sq_nonneg _
      nlinarith
    have hint_rhs : Integrable (fun ω =>
        (2 * (a * τ k) ^ 2) * ‖w k ω‖ ^ 2 + (2 * (a * τ k) ^ 2) * ‖z k ω‖ ^ 2) μ :=
      ((integrable_norm_sq_of_memLp (hw_lp k)).const_mul _).add
        ((integrable_norm_sq_of_memLp (hz_lp k)).const_mul _)
    have h1 : ∫ ω, ‖z (k + 1) ω - z k ω‖ ^ 2 ∂μ ≤
        4 * a ^ 2 * σJ ^ 2 * σs ^ 2 * τ k ^ 2 := by
      calc ∫ ω, ‖z (k + 1) ω - z k ω‖ ^ 2 ∂μ
          ≤ ∫ ω, ((2 * (a * τ k) ^ 2) * ‖w k ω‖ ^ 2 +
              (2 * (a * τ k) ^ 2) * ‖z k ω‖ ^ 2) ∂μ :=
            integral_mono (hz_diff_int k) hint_rhs hpt
        _ = (2 * (a * τ k) ^ 2) * ∫ ω, ‖w k ω‖ ^ 2 ∂μ +
            (2 * (a * τ k) ^ 2) * ∫ ω, ‖z k ω‖ ^ 2 ∂μ := by
            rw [integral_add ((integrable_norm_sq_of_memLp (hw_lp k)).const_mul _)
              ((integrable_norm_sq_of_memLp (hz_lp k)).const_mul _),
              integral_const_mul, integral_const_mul]
        _ ≤ (2 * (a * τ k) ^ 2) * (σJ ^ 2 * σs ^ 2) +
            (2 * (a * τ k) ^ 2) * (σJ ^ 2 * σs ^ 2) := by
            have hnn : 0 ≤ 2 * (a * τ k) ^ 2 := by positivity
            nlinarith [hw_sq_le k, hz_sq_le_pos k hk]
        _ = 4 * a ^ 2 * σJ ^ 2 * σs ^ 2 * τ k ^ 2 := by ring
    have hnn : 0 ≤ a ^ 2 * σJ ^ 2 * σs ^ 2 * τ k ^ 2 := by positivity
    linarith
  have hz_diff_sum : ∀ N : ℕ,
      ∑ k ∈ Finset.range N, ∫ ω, ‖z (k + 1) ω - z k ω‖ ^ 2 ∂μ ≤
        2 * (‖z0‖ ^ 2 + 24 * a ^ 2 * σJ ^ 2 * σs ^ 2 * ∑ k ∈ Finset.range N, τ k ^ 2) := by
    intro N
    cases N with
    | zero =>
      simp only [Finset.range_zero, Finset.sum_empty, mul_zero, add_zero]
      positivity
    | succ M =>
      rw [Finset.sum_range_succ', Finset.sum_range_succ']
      have htail : ∑ k ∈ Finset.range M, ∫ ω, ‖z (k + 1 + 1) ω - z (k + 1) ω‖ ^ 2 ∂μ ≤
          ∑ k ∈ Finset.range M, 48 * a ^ 2 * σJ ^ 2 * σs ^ 2 * τ (k + 1) ^ 2 :=
        Finset.sum_le_sum fun k _ => hz_diff_pos (k + 1) (Nat.succ_le_succ (Nat.zero_le k))
      rw [← Finset.mul_sum] at htail
      linarith [hz_diff_0, htail]
  exact ⟨hd_sm, hd_lp, hd_sq_le, hx_succ_sm, hgx_lp, hu_lp, hz_diff_int, hz_diff_sum⟩

private lemma continuous_Cterm_map {n m : ℕ}
    {f : EuclideanSpace ℝ (Fin m) → ℝ}
    {g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}
    {Lf Lg Ldf Ldg : ℝ} (hA2 : Assumption2 f g Lf Lg Ldf Ldg) :
    Continuous (Function.uncurry
      (fun (x : EuclideanSpace ℝ (Fin n)) (u : EuclideanSpace ℝ (Fin m)) =>
        (ContinuousLinearMap.adjoint (fderiv ℝ g x)) (gradient f u))) :=
  (ContinuousLinearMap.adjoint.continuous.comp
    ((continuous_fderiv_g hA2).comp continuous_fst)).clm_apply
    ((continuous_gradient_f hA2).comp continuous_snd)

/-- Integrability and single-step expectation bound for `rTerm`. -/
private lemma rTerm_integrable_and_exp_le {n m : ℕ} {Ω : Type*} [mΩ : MeasurableSpace Ω]
    [StandardBorelSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ] {ℱ : Filtration ℕ mΩ}
    {P : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    {f : EuclideanSpace ℝ (Fin m) → ℝ}
    {g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}
    {Lf Lg Ldf Ldg : ℝ} (hA2 : Assumption2 f g Lf Lg Ldf Ldg)
    {a : ℝ} (b : ℝ) {γ β : ℝ} (ha_pos : 0 < a) (hγ : 0 < γ) (τ : ℕ → ℝ)
    {z0 : EuclideanSpace ℝ (Fin n)}
    {x z : ℕ → Ω → EuclideanSpace ℝ (Fin n)} {u G s : ℕ → Ω → EuclideanSpace ℝ (Fin m)}
    {J : ℕ → Ω → (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m))}
    {σG σJ σs : ℝ} (hA1 : Assumption1 μ ℱ f g x z u G s J σG σJ σs)
    (hd_sm : ∀ k, StronglyMeasurable[ℱ k] (fun ω => ybar P (x k ω) (z k ω) β - x k ω))
    (hd_lp : ∀ k, MemLp (fun ω => ybar P (x k ω) (z k ω) β - x k ω) 2 μ)
    (hd_sq_le : ∀ k, ∫ ω, ‖ybar P (x k ω) (z k ω) β - x k ω‖ ^ 2 ∂μ ≤
        max (σJ ^ 2 * σs ^ 2) (‖z0‖ ^ 2) / β ^ 2)
    (hx_succ_sm : ∀ k, StronglyMeasurable[ℱ k] (x (k + 1)))
    (hgx_lp : ∀ k, MemLp (fun ω => g (x (k + 1) ω)) 2 μ)
    (hu_lp : ∀ k, MemLp (u k) 2 μ)
    (hz_diff_int : ∀ k, Integrable (fun ω => ‖z (k + 1) ω - z k ω‖ ^ 2) μ) (k : ℕ) :
    Integrable (fun ω => rTerm P f g a b γ β Lf Lg Ldf Ldg τ
        (fun i => x i ω) (fun i => z i ω) (fun i => u i ω) (fun i => G i ω)
        (fun i => s i ω) (fun i => J i ω) k) μ ∧
    ∫ ω, rTerm P f g a b γ β Lf Lg Ldf Ldg τ
        (fun i => x i ω) (fun i => z i ω) (fun i => u i ω) (fun i => G i ω)
        (fun i => s i ω) (fun i => J i ω) k ∂μ ≤
      τ k ^ 2 / 2 * ((a * LgradF Lf Lg Ldf Ldg + Leta β + γ * Lg ^ 2 + 2 * a * Lg ^ 2 * Ldf) *
          max (σJ ^ 2 * σs ^ 2) (‖z0‖ ^ 2) / β ^ 2 + γ * b ^ 2 * σG ^ 2) +
        Leta β / 2 * ∫ ω, ‖z (k + 1) ω - z k ω‖ ^ 2 ∂μ := by
  let w : Ω → EuclideanSpace ℝ (Fin n) :=
    fun ω => (ContinuousLinearMap.adjoint (J (k + 1) ω)) (s (k + 1) ω)
  let d : Ω → EuclideanSpace ℝ (Fin n) :=
    fun ω => ybar P (x k ω) (z k ω) β - x k ω
  let Cterm : Ω → EuclideanSpace ℝ (Fin n) :=
    fun ω => (ContinuousLinearMap.adjoint (fderiv ℝ g (x (k + 1) ω))) (gradient f (u k ω))
  have hw_lp : MemLp w 2 μ := (oracle_prod_memLp_and_sq_le hA1 k).1
  have hw_ce : μ[w | ℱ k] =ᵐ[μ] Cterm := oracle_prod_condExp hA1 k hw_lp
  have hC_sm : StronglyMeasurable[ℱ k] Cterm :=
    stronglyMeasurable_comp₂ (continuous_Cterm_map hA2) (hx_succ_sm k) (hA1.adapted_u k)
  have hC_lp : MemLp Cterm 2 μ := by
    refine MemLp.of_bound (hC_sm.mono (ℱ.le k)).aestronglyMeasurable (Lg * Lf)
      (Filter.Eventually.of_forall fun ω => ?_)
    calc ‖Cterm ω‖
        ≤ ‖ContinuousLinearMap.adjoint (fderiv ℝ g (x (k + 1) ω))‖ * ‖gradient f (u k ω)‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ = ‖fderiv ℝ g (x (k + 1) ω)‖ * ‖gradient f (u k ω)‖ := by
          rw [LinearIsometryEquiv.norm_map]
      _ ≤ Lg * Lf :=
          mul_le_mul (norm_fderiv_g_le hA2 _) (norm_gradient_f_le hA2 _) (norm_nonneg _)
            hA2.Lg_nonneg
  have hG_err_lp : MemLp (fun ω => g (x (k + 1) ω) - G (k + 1) ω) 2 μ :=
    (hgx_lp k).sub (hA1.memLp_G k)
  have hG_err_sq_int : Integrable (fun ω => ‖g (x (k + 1) ω) - G (k + 1) ω‖ ^ 2) μ :=
    integrable_norm_sq_of_memLp hG_err_lp
  have hG_err_sq_le : ∫ ω, ‖g (x (k + 1) ω) - G (k + 1) ω‖ ^ 2 ∂μ ≤ σG ^ 2 := by
    have hrev : (fun ω => ‖g (x (k + 1) ω) - G (k + 1) ω‖ ^ 2) =
        fun ω => ‖G (k + 1) ω - g (x (k + 1) ω)‖ ^ 2 :=
      funext fun ω => by rw [norm_sub_rev]
    rw [hrev]
    calc ∫ ω, ‖G (k + 1) ω - g (x (k + 1) ω)‖ ^ 2 ∂μ
        = ∫ ω, μ[fun ω => ‖G (k + 1) ω - g (x (k + 1) ω)‖ ^ 2 | ℱ k] ω ∂μ :=
          (integral_condExp (ℱ.le k)).symm
      _ ≤ ∫ _ω, σG ^ 2 ∂μ :=
          integral_mono_ae integrable_condExp (integrable_const _) (hA1.condExp_G_var k)
      _ = σG ^ 2 := by rw [integral_const]; simp
  have hterm3_int : Integrable (fun ω =>
      ⟪g (x (k + 1) ω) - u k ω, g (x (k + 1) ω) - G (k + 1) ω⟫) μ :=
    integrable_inner_of_memLp ((hgx_lp k).sub (hu_lp k)) hG_err_lp
  have hterm3_zero : ∫ ω,
      ⟪g (x (k + 1) ω) - u k ω, g (x (k + 1) ω) - G (k + 1) ω⟫ ∂μ = 0 := by
    have hgx_sm : StronglyMeasurable[ℱ k] (fun ω => g (x (k + 1) ω)) :=
      (continuous_g hA2).comp_stronglyMeasurable (hx_succ_sm k)
    have hA_sm : StronglyMeasurable[ℱ k] (fun ω => g (x (k + 1) ω) - u k ω) :=
      hgx_sm.sub (hA1.adapted_u k)
    have hB_ce : μ[fun ω => g (x (k + 1) ω) - G (k + 1) ω | ℱ k] =ᵐ[μ] 0 := by
      have hsub := condExp_sub ((hgx_lp k).integrable one_le_two)
        ((hA1.memLp_G k).integrable one_le_two) (ℱ k)
      have hself : μ[fun ω => g (x (k + 1) ω) | ℱ k] = fun ω => g (x (k + 1) ω) :=
        condExp_of_stronglyMeasurable (ℱ.le k) hgx_sm ((hgx_lp k).integrable one_le_two)
      filter_upwards [hsub, hA1.condExp_G k] with ω h1 h2
      change (μ[(fun ω => g (x (k + 1) ω)) - G (k + 1) | ℱ k]) ω = 0
      rw [h1]
      simp only [Pi.sub_apply, hself, h2, sub_self]
    exact integral_inner_eq_zero_of_condExp_zero (ℱ.le k) hA_sm ((hgx_lp k).sub (hu_lp k))
      hG_err_lp hB_ce
  have hterm4_int : Integrable (fun ω => ⟪d ω, Cterm ω - w ω⟫) μ :=
    integrable_inner_of_memLp (hd_lp k) (hC_lp.sub hw_lp)
  have hterm4_zero : ∫ ω, ⟪d ω, Cterm ω - w ω⟫ ∂μ = 0 := by
    have hB_ce : μ[fun ω => Cterm ω - w ω | ℱ k] =ᵐ[μ] 0 := by
      have hsub := condExp_sub (hC_lp.integrable one_le_two) (hw_lp.integrable one_le_two) (ℱ k)
      have hself : μ[Cterm | ℱ k] = Cterm :=
        condExp_of_stronglyMeasurable (ℱ.le k) hC_sm (hC_lp.integrable one_le_two)
      filter_upwards [hsub, hw_ce] with ω h1 h2
      change (μ[Cterm - w | ℱ k]) ω = 0
      rw [h1]
      simp only [Pi.sub_apply, hself, h2, sub_self]
    exact integral_inner_eq_zero_of_condExp_zero (ℱ.le k) (hd_sm k) (hd_lp k)
      (hC_lp.sub hw_lp) hB_ce
  set c_d : ℝ := a * LgradF Lf Lg Ldf Ldg + Leta β + γ * Lg ^ 2 + 2 * a * Lg ^ 2 * Ldf
  have hLeta_nonneg : 0 ≤ Leta β := by unfold Leta; positivity
  have hcd_nonneg : 0 ≤ c_d := by
    dsimp [c_d, LgradF]
    have := hA2.Lf_nonneg
    have := hA2.Lg_nonneg
    have := hA2.Ldf_nonneg
    have := hA2.Ldg_nonneg
    positivity
  have hparts := integrable_and_integral_rTerm_parts (c_d := c_d) (γ := γ) (b := b) (τk := τ k)
    (a := a) (Letaβ := Leta β)
    (integrable_norm_sq_of_memLp (hd_lp k)) hG_err_sq_int hterm3_int hterm4_int (hz_diff_int k)
    hterm3_zero hterm4_zero
  unfold rTerm
  refine ⟨hparts.1, ?_⟩
  rw [hparts.2]
  have hτ2 : 0 ≤ τ k ^ 2 / 2 := by positivity
  have hγb2 : 0 ≤ γ * b ^ 2 := by positivity
  have hd_bnd : c_d * ∫ ω, ‖d ω‖ ^ 2 ∂μ ≤
      c_d * max (σJ ^ 2 * σs ^ 2) (‖z0‖ ^ 2) / β ^ 2 := by
    have := mul_le_mul_of_nonneg_left (hd_sq_le k) hcd_nonneg
    rwa [← mul_div_assoc] at this
  have hG_bnd : γ * b ^ 2 * ∫ ω, ‖g (x (k + 1) ω) - G (k + 1) ω‖ ^ 2 ∂μ ≤ γ * b ^ 2 * σG ^ 2 :=
    mul_le_mul_of_nonneg_left hG_err_sq_le hγb2
  nlinarith

end NestedSAProp1bAux

open NestedSAProp1bAux

theorem solution {n m : ℕ} {Ω : Type*} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ℱ : Filtration ℕ mΩ)
    (X : Set (EuclideanSpace ℝ (Fin n))) (hX_cl : IsClosed X) (hX_cvx : Convex ℝ X)
    (P : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hP : SpectralProjGrad.Shared.IsProjOnto X P)
    (f : EuclideanSpace ℝ (Fin m) → ℝ) (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m))
    (Lf Lg Ldf Ldg : ℝ) (hA2 : Assumption2 f g Lf Lg Ldf Ldg)
    (a b β : ℝ) (τ : ℕ → ℝ) (x0 z0 : EuclideanSpace ℝ (Fin n)) (u0 : EuclideanSpace ℝ (Fin m))
    (x z : ℕ → Ω → EuclideanSpace ℝ (Fin n)) (u G s : ℕ → Ω → EuclideanSpace ℝ (Fin m))
    (J : ℕ → Ω → (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m)))
    (hrun : IsStochRun X P a b β τ x0 z0 u0 x z u G s J)
    (σG σJ σs : ℝ) (hA1 : Assumption1 μ ℱ f g x z u G s J σG σJ σs)
    (γ : ℝ) (hγ : 0 < γ)
    (hτ_one : ∀ k, τ k ≤ 1) (hτ0 : τ 0 = 1 / a)
    (haτ : ∀ k, 1 ≤ k → a * τ k ≤ 1 / Real.sqrt 2) :
    ∀ N : ℕ,
      (∀ k, Integrable (fun ω => ‖z (k + 1) ω - z k ω‖ ^ 2) μ) ∧
      (∀ k, Integrable (fun ω => rTerm P f g a b γ β Lf Lg Ldf Ldg τ (fun i => x i ω) (fun i => z i ω)
          (fun i => u i ω) (fun i => G i ω) (fun i => s i ω) (fun i => J i ω) k) μ) ∧
      ∑ k ∈ Finset.range N, ∫ ω, ‖z (k + 1) ω - z k ω‖ ^ 2 ∂μ ≤
        2 * (‖z0‖ ^ 2 + 24 * a ^ 2 * σJ ^ 2 * σs ^ 2 * ∑ k ∈ Finset.range N, τ k ^ 2) ∧
      ∑ k ∈ Finset.range N, ∫ ω, rTerm P f g a b γ β Lf Lg Ldf Ldg τ (fun i => x i ω) (fun i => z i ω)
          (fun i => u i ω) (fun i => G i ω) (fun i => s i ω) (fun i => J i ω) k ∂μ ≤
        sigmaHatSq a b γ β Lf Lg Ldf Ldg σG σJ σs z0 * ∑ k ∈ Finset.range N, τ k ^ 2 := by
  have _ := hX_cl
  have _ := haτ
  obtain ⟨ω₀⟩ := nonempty_of_isProbabilityMeasure μ
  have ha_pos : 0 < a := (hrun ω₀).a_pos
  have hβ_pos : 0 < β := (hrun ω₀).β_pos
  have hτ_pos : ∀ k, 0 < τ k := (hrun ω₀).τ_pos
  have hτ_le : ∀ k, τ k ≤ 1 / a := (hrun ω₀).τ_le
  obtain ⟨hd_sm, hd_lp, hd_sq_le, hx_succ_sm, hgx_lp, hu_lp, hz_diff_int, hz_diff_sum⟩ :=
    iterate_moment_bounds hX_cvx hP hA2 hrun hA1 ha_pos hβ_pos hτ_pos hτ_le hτ_one hτ0
  have hr_all := fun k => rTerm_integrable_and_exp_le hA2 b ha_pos hγ τ hA1 hd_sm hd_lp hd_sq_le
    hx_succ_sm hgx_lp hu_lp hz_diff_int k
  have hr_int := fun k => (hr_all k).1
  have hr_exp_le := fun k => (hr_all k).2
  have hLeta_nonneg : 0 ≤ Leta β := by unfold Leta; positivity
  set c_d : ℝ := a * LgradF Lf Lg Ldf Ldg + Leta β + γ * Lg ^ 2 + 2 * a * Lg ^ 2 * Ldf
  intro N
  refine ⟨hz_diff_int, hr_int, hz_diff_sum N, ?_⟩
  cases N with
  | zero => simp
  | succ M =>
    set S : ℝ := ∑ k ∈ Finset.range (M + 1), τ k ^ 2
    have hS_ge : 1 / a ^ 2 ≤ S := by
      have h0 : τ 0 ^ 2 ≤ S :=
        Finset.single_le_sum (fun k _ => sq_nonneg (τ k)) (Finset.mem_range.mpr (Nat.zero_lt_succ M))
      rwa [hτ0, one_div_pow] at h0
    have ha2S : 1 ≤ a ^ 2 * S := by
      have := mul_le_mul_of_nonneg_left hS_ge (sq_nonneg a)
      rwa [mul_one_div_cancel (pow_ne_zero 2 ha_pos.ne')] at this
    have hsum_r : ∑ k ∈ Finset.range (M + 1), ∫ ω, rTerm P f g a b γ β Lf Lg Ldf Ldg τ
          (fun i => x i ω) (fun i => z i ω) (fun i => u i ω) (fun i => G i ω)
          (fun i => s i ω) (fun i => J i ω) k ∂μ ≤
        1 / 2 * (c_d * max (σJ ^ 2 * σs ^ 2) (‖z0‖ ^ 2) / β ^ 2 + γ * b ^ 2 * σG ^ 2) * S +
          Leta β / 2 * ∑ k ∈ Finset.range (M + 1), ∫ ω, ‖z (k + 1) ω - z k ω‖ ^ 2 ∂μ := by
      calc ∑ k ∈ Finset.range (M + 1), ∫ ω, rTerm P f g a b γ β Lf Lg Ldf Ldg τ
              (fun i => x i ω) (fun i => z i ω) (fun i => u i ω) (fun i => G i ω)
              (fun i => s i ω) (fun i => J i ω) k ∂μ
          ≤ ∑ k ∈ Finset.range (M + 1),
              (τ k ^ 2 / 2 * (c_d * max (σJ ^ 2 * σs ^ 2) (‖z0‖ ^ 2) / β ^ 2 + γ * b ^ 2 * σG ^ 2) +
                Leta β / 2 * ∫ ω, ‖z (k + 1) ω - z k ω‖ ^ 2 ∂μ) :=
            Finset.sum_le_sum fun k _ => hr_exp_le k
        _ = (∑ k ∈ Finset.range (M + 1),
              τ k ^ 2 / 2 * (c_d * max (σJ ^ 2 * σs ^ 2) (‖z0‖ ^ 2) / β ^ 2 + γ * b ^ 2 * σG ^ 2)) +
            ∑ k ∈ Finset.range (M + 1), Leta β / 2 * ∫ ω, ‖z (k + 1) ω - z k ω‖ ^ 2 ∂μ :=
            Finset.sum_add_distrib
        _ = 1 / 2 * (c_d * max (σJ ^ 2 * σs ^ 2) (‖z0‖ ^ 2) / β ^ 2 + γ * b ^ 2 * σG ^ 2) * S +
            Leta β / 2 * ∑ k ∈ Finset.range (M + 1), ∫ ω, ‖z (k + 1) ω - z k ω‖ ^ 2 ∂μ := by
            rw [← Finset.mul_sum]
            congr 1
            have : ∀ k, τ k ^ 2 / 2 *
                (c_d * max (σJ ^ 2 * σs ^ 2) (‖z0‖ ^ 2) / β ^ 2 + γ * b ^ 2 * σG ^ 2) =
                1 / 2 * (c_d * max (σJ ^ 2 * σs ^ 2) (‖z0‖ ^ 2) / β ^ 2 + γ * b ^ 2 * σG ^ 2) *
                  τ k ^ 2 := fun k => by ring
            simp_rw [this, ← Finset.mul_sum]
            rfl
    have hz_term : Leta β / 2 * ∑ k ∈ Finset.range (M + 1), ∫ ω, ‖z (k + 1) ω - z k ω‖ ^ 2 ∂μ ≤
        2 * Leta β * (max 1 (a ^ 2 / 2) * ‖z0‖ ^ 2 + 24 * a ^ 2 * σJ ^ 2 * σs ^ 2) * S := by
      have h1 : Leta β / 2 * ∑ k ∈ Finset.range (M + 1), ∫ ω, ‖z (k + 1) ω - z k ω‖ ^ 2 ∂μ ≤
          Leta β * ‖z0‖ ^ 2 + Leta β * (24 * a ^ 2 * σJ ^ 2 * σs ^ 2) * S := by
        have := mul_le_mul_of_nonneg_left (hz_diff_sum (M + 1)) (div_nonneg hLeta_nonneg zero_le_two)
        linarith
      have hmax : a ^ 2 / 2 ≤ max 1 (a ^ 2 / 2) := le_max_right _ _
      have h2 : 1 ≤ 2 * max 1 (a ^ 2 / 2) * S := by
        have hS_nn : 0 ≤ S := Finset.sum_nonneg fun _ _ => sq_nonneg _
        nlinarith
      have h3 : Leta β * ‖z0‖ ^ 2 ≤ 2 * Leta β * max 1 (a ^ 2 / 2) * ‖z0‖ ^ 2 * S := by
        have hnn : 0 ≤ Leta β * ‖z0‖ ^ 2 := by positivity
        nlinarith
      have h4 : Leta β * (24 * a ^ 2 * σJ ^ 2 * σs ^ 2) * S ≤
          2 * Leta β * (24 * a ^ 2 * σJ ^ 2 * σs ^ 2) * S := by
        have hS_nn : 0 ≤ S := Finset.sum_nonneg fun _ _ => sq_nonneg _
        have hnn : 0 ≤ Leta β * (24 * a ^ 2 * σJ ^ 2 * σs ^ 2) * S := by positivity
        linarith
      linarith
    unfold sigmaHatSq
    dsimp only [c_d] at hsum_r
    linarith
