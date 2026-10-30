-- Prove2me | solution 1 for MHSpectralGap.RWM.acceptance_bound
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-29T22:22:37.651523+00:00
-- url     : https://prove2.me/submissions/c2556cee-ab67-4090-813b-0dfacb521335

import Mathlib
import Definitions.Def_MHSpectralGap_RWM_RWMKernel
import Definitions.Def_MHSpectralGap_RWM_Conductance

open MeasureTheory ProbabilityTheory Real
set_option autoImplicit false
open scoped ENNReal NNReal BigOperators

namespace MHSpectralGap.RWM

/-- The normalisation algebra behind `integral_exp_neg_quad_linear`. -/
lemma sqrt_factor {v A B : ℝ} (hv : 0 < v) (hA : 0 < A) :
    (√(2 * π * v))⁻¹ * Real.exp (B ^ 2 / (4 * (A + (2 * v)⁻¹))) * √(π / (A + (2 * v)⁻¹))
      = (√(1 + 2 * v * A))⁻¹ * Real.exp (B ^ 2 * v / (2 * (1 + 2 * v * A))) := by
  have hπ : (0 : ℝ) < π := pi_pos
  set Ap : ℝ := A + (2 * v)⁻¹ with hAp
  have hAp0 : 0 < Ap := by rw [hAp]; positivity
  have hvAp : 2 * v * Ap = 1 + 2 * v * A := by
    rw [hAp]
    field_simp
    ring
  have hexp : B ^ 2 / (4 * Ap) = B ^ 2 * v / (2 * (1 + 2 * v * A)) := by
    rw [← hvAp]
    field_simp
    ring
  have hsqrt : (√(2 * π * v))⁻¹ * √(π / Ap) = (√(1 + 2 * v * A))⁻¹ := by
    rw [← hvAp]
    refine (sq_eq_sq₀ (by positivity) (by positivity)).mp ?_
    rw [mul_pow, inv_pow, inv_pow,
      Real.sq_sqrt (x := 2 * π * v) (by positivity),
      Real.sq_sqrt (x := π / Ap) (by positivity),
      Real.sq_sqrt (x := 2 * v * Ap) (by positivity)]
    field_simp
  rw [hexp, mul_right_comm, hsqrt]

/-- **The one-dimensional Gaussian integral with quadratic and linear terms**:
`∫ exp (-(A τ² + B τ)) N(0, v)(dτ) = (1 + 2 v A)^{-1/2} exp (B² v / (2 (1 + 2 v A)))`. -/
lemma integral_exp_neg_quad_linear {v : ℝ≥0} (hv : v ≠ 0) {A B : ℝ} (hA : 0 < A) :
    ∫ τ : ℝ, Real.exp (-(A * τ ^ 2 + B * τ)) ∂(gaussianReal 0 v) =
      (√(1 + 2 * (v : ℝ) * A))⁻¹ *
        Real.exp (B ^ 2 * (v : ℝ) / (2 * (1 + 2 * (v : ℝ) * A))) := by
  have hvpos : (0 : ℝ) < (v : ℝ) := NNReal.coe_pos.mpr (zero_lt_iff.mpr hv)
  set Ap : ℝ := A + (2 * (v : ℝ))⁻¹ with hAp
  have hAppos : 0 < Ap := by rw [hAp]; positivity
  rw [integral_gaussianReal_eq_integral_smul
    (f := fun τ : ℝ => Real.exp (-(A * τ ^ 2 + B * τ))) hv]
  have hpoint : ∀ τ : ℝ,
      gaussianPDFReal 0 v τ • Real.exp (-(A * τ ^ 2 + B * τ)) =
        (√(2 * π * (v : ℝ)))⁻¹ * Real.exp (B ^ 2 / (4 * Ap)) *
          Real.exp (-Ap * (τ + B / (2 * Ap)) ^ 2) := by
    intro τ
    have harg : -τ ^ 2 / (2 * (v : ℝ)) + -(A * τ ^ 2 + B * τ)
        = B ^ 2 / (4 * Ap) + (-Ap * (τ + B / (2 * Ap)) ^ 2) := by
      rw [hAp]
      field_simp
      ring
    simp only [gaussianPDFReal, sub_zero, smul_eq_mul]
    rw [mul_assoc, ← Real.exp_add, harg, Real.exp_add, ← mul_assoc]
  simp_rw [hpoint]
  rw [integral_const_mul]
  have hshift : ∫ τ : ℝ, Real.exp (-Ap * (τ + B / (2 * Ap)) ^ 2) =
      ∫ τ : ℝ, Real.exp (-Ap * τ ^ 2) :=
    integral_add_right_eq_self (μ := (volume : Measure ℝ))
      (fun y : ℝ => Real.exp (-Ap * y ^ 2)) (B / (2 * Ap))
  rw [hshift, integral_gaussian Ap]
  exact sqrt_factor hvpos hA

/-! ### B. The proposal as a pushforward of `gammaM`, and the coordinate factorisation -/

lemma rwmProposal_apply (m : ℕ) (δ : ℝ) (x : Fin m → ℝ) :
    rwmProposal m δ x = (gammaM m).map (fun ξ : Fin m → ℝ => x + Real.sqrt (2 * δ) • ξ) := by
  rw [rwmProposal, Kernel.map_apply _ (by fun_prop)]
  rw [Kernel.prod_apply, Kernel.id_apply, Kernel.const_apply, Measure.dirac_prod]
  rw [Measure.map_map (by fun_prop) (by fun_prop)]
  rfl

lemma measurable_rwmAccept (m : ℕ) (x : Fin m → ℝ) : Measurable (rwmAccept m x) := by
  unfold rwmAccept
  fun_prop

lemma accBar_rwm (m : ℕ) (δ : ℝ) (x : Fin m → ℝ) :
    accBar (rwmProposal m δ) (rwmAccept m) x =
      ∫⁻ ξ : Fin m → ℝ, rwmAccept m x (x + Real.sqrt (2 * δ) • ξ) ∂(gammaM m) := by
  rw [accBar, rwmProposal_apply,
    lintegral_map (f := fun y : Fin m → ℝ => rwmAccept m x y)
      (measurable_rwmAccept m x) (by fun_prop)]

/-- The product decomposition of a Gaussian spectral expectation over `gammaM m`. -/
theorem integral_exp_sum_gammaM {m : ℕ} (A B : Fin m → ℝ) :
    ∫ ξ : Fin m → ℝ, Real.exp (-(∑ i, (A i * ξ i ^ 2 + B i * ξ i))) ∂(gammaM m) =
      ∏ i : Fin m, ∫ τ : ℝ, Real.exp (-(A i * τ ^ 2 + B i * τ))
        ∂(gaussianReal 0 (1 / ((i : ℝ≥0) + 1) ^ 2)) := by
  rw [gammaM]
  rw [show (fun ξ : Fin m → ℝ => Real.exp (-(∑ i, (A i * ξ i ^ 2 + B i * ξ i))))
      = fun ξ => ∏ i, Real.exp (-(A i * ξ i ^ 2 + B i * ξ i)) from by
    funext ξ
    rw [← Real.exp_sum]
    congr 1
    rw [Finset.sum_neg_distrib]]
  exact integral_fintype_prod_eq_prod
    (μ := fun i : Fin m => gaussianReal 0 (1 / ((i : ℝ≥0) + 1) ^ 2))
    (f := fun i τ => Real.exp (-(A i * τ ^ 2 + B i * τ)))

/-! ### C. The acceptance probability at the proposed point -/

/-- At the proposal `x + √(2δ) ξ` the acceptance probability is `1 ∧ exp (-S ξ)`. -/
lemma rwmAccept_add_smul (m : ℕ) (δ : ℝ) (hδ : 0 ≤ δ) (x ξ : Fin m → ℝ) :
    rwmAccept m x (x + Real.sqrt (2 * δ) • ξ) =
      ENNReal.ofReal (min 1 (Real.exp (-(∑ i : Fin m,
        ((i : ℝ) + 1) ^ 2 * (δ * ξ i ^ 2 + Real.sqrt (2 * δ) * x i * ξ i))))) := by
  have hmain : (∑ i : Fin m, ((i : ℝ) + 1) ^ 2 / 2 *
      (x i ^ 2 - (x + Real.sqrt (2 * δ) • ξ) i ^ 2)) =
      -(∑ i : Fin m, ((i : ℝ) + 1) ^ 2 *
        (δ * ξ i ^ 2 + Real.sqrt (2 * δ) * x i * ξ i)) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have hs2 : Real.sqrt (δ * 2) ^ 2 = 2 * δ := by
      rw [mul_comm δ 2]
      exact Real.sq_sqrt (by linarith)
    ring_nf
    rw [hs2]
    ring
  rw [rwmAccept, hmain]

/-- `min 1 e^{-S} ≤ e^{-λS}` for `λ ∈ [0, 1]`. -/
lemma min_one_exp_le {S lam : ℝ} (h0 : 0 ≤ lam) (h1 : lam ≤ 1) :
    min 1 (Real.exp (-S)) ≤ Real.exp (-(lam * S)) := by
  by_cases hS : 0 ≤ S
  · have hle : -S ≤ -(lam * S) := by nlinarith
    exact le_trans (min_le_right _ _) (Real.exp_le_exp.mpr hle)
  · push_neg at hS
    rw [min_eq_left]
    · rw [← Real.exp_zero]
      exact Real.exp_le_exp.mpr (by nlinarith)
    · rw [← Real.exp_zero]
      exact Real.exp_le_exp.mpr (by linarith)

/-- The AM-GM bound behind integrability: `-(A τ² + B τ) ≤ B² / (4 A)` for `A > 0`. -/
lemma neg_quad_le (A B τ : ℝ) (hA : 0 < A) : -(A * τ ^ 2 + B * τ) ≤ B ^ 2 / (4 * A) := by
  have h : 0 ≤ (2 * A * τ + B) ^ 2 := sq_nonneg _
  have heq : 4 * A * (A * τ ^ 2 + B * τ) + B ^ 2 = (2 * A * τ + B) ^ 2 := by ring
  have h4 : 0 < 4 * A := by positivity
  rw [le_div_iff₀ h4]
  nlinarith [h, heq]

/-- Integrability of a Gaussian spectral weight over `gammaM m`. -/
lemma integrable_exp_neg_quad_sum {m : ℕ} (A B : Fin m → ℝ) (hA : ∀ i, 0 < A i) :
    Integrable (fun ξ : Fin m → ℝ => Real.exp (-(∑ i, (A i * ξ i ^ 2 + B i * ξ i))))
      (gammaM m) := by
  have hbound : ∀ ξ : Fin m → ℝ,
      Real.exp (-(∑ i, (A i * ξ i ^ 2 + B i * ξ i))) ≤
        Real.exp (∑ i, B i ^ 2 / (4 * A i)) := by
    intro ξ
    refine Real.exp_le_exp.mpr ?_
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => neg_quad_le (A i) (B i) (ξ i) (hA i)
  refine Integrable.of_bound (C := Real.exp (∑ i, B i ^ 2 / (4 * A i))) ?_ ?_
  · fun_prop
  · filter_upwards with ξ
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact hbound ξ

/-! ### D. The acceptance bound -/

lemma inv_sqrt_pow (c : ℝ) (hc : 0 < c) (m : ℕ) :
    ((√c)⁻¹) ^ m = c ^ (-(m : ℝ) / 2) := by
  rw [inv_pow, Real.sqrt_eq_rpow, ← Real.rpow_natCast _ m, ← Real.rpow_mul hc.le,
    ← Real.rpow_neg hc.le]
  congr 1
  ring

theorem acceptance_bound_aux (m : ℕ) (δ : ℝ) (hδ : 0 < δ) (lam : ℝ) (hlam : lam ∈ Set.Icc (0 : ℝ) 1)
    (x : Fin m → ℝ) :
    accBar (rwmProposal m δ) (rwmAccept m) x ≤
      ENNReal.ofReal ((1 + 2 * lam * δ) ^ (-(m : ℝ) / 2) *
        Real.exp (∑ i : Fin m, δ * lam ^ 2 * ((i : ℝ) + 1) ^ 2 * x i ^ 2 / (2 * δ * lam + 1))) := by
  have hδ0 : 0 ≤ δ := le_of_lt hδ
  have hlam0 : 0 ≤ lam := hlam.1
  have hlam1 : lam ≤ 1 := hlam.2
  rcases lt_or_eq_of_le hlam0 with hpos | hzero
  swap
  · -- `λ = 0`: both sides are `1`
    subst hzero
    have hle1 : accBar (rwmProposal m δ) (rwmAccept m) x ≤ 1 := by
      rw [accBar]
      calc ∫⁻ y, rwmAccept m x y ∂(rwmProposal m δ x)
          ≤ ∫⁻ _y, (1 : ℝ≥0∞) ∂(rwmProposal m δ x) := by
            refine lintegral_mono fun y => ?_
            rw [rwmAccept]
            refine le_trans (ENNReal.ofReal_le_ofReal (min_le_left (1 : ℝ) _)) (le_of_eq ?_)
            exact ENNReal.ofReal_one
        _ = 1 := by rw [lintegral_one]; simp
    refine le_trans hle1 (le_of_eq ?_)
    have h1 : (1 + 2 * (0 : ℝ) * δ) ^ (-(m : ℝ) / 2) *
        Real.exp (∑ i : Fin m, δ * (0 : ℝ) ^ 2 * ((i : ℝ) + 1) ^ 2 * x i ^ 2 /
          (2 * δ * 0 + 1)) = 1 := by
      simp
    rw [h1, ENNReal.ofReal_one]
  -- main case `λ > 0`
  set A : Fin m → ℝ := fun i => lam * δ * ((i : ℝ) + 1) ^ 2 with hAdef
  set B : Fin m → ℝ := fun i => lam * Real.sqrt (2 * δ) * ((i : ℝ) + 1) ^ 2 * x i with hBdef
  have hApos : ∀ i : Fin m, 0 < A i := by
    intro i
    rw [hAdef]
    have : (0 : ℝ) < ((i : ℝ) + 1) ^ 2 := by positivity
    positivity
  have hvco : ∀ i : Fin m, ((1 / ((i : ℝ≥0) + 1) ^ 2 : ℝ≥0) : ℝ) = 1 / (((i : ℝ) + 1) ^ 2) := by
    intro i
    norm_num
  have hS_eq : ∀ ξ : Fin m → ℝ, lam * (∑ i : Fin m, ((i : ℝ) + 1) ^ 2 *
      (δ * ξ i ^ 2 + Real.sqrt (2 * δ) * x i * ξ i)) =
      ∑ i : Fin m, (A i * ξ i ^ 2 + B i * ξ i) := by
    intro ξ
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [hAdef, hBdef]
    ring
  -- the one-coordinate evaluation
  have hcoord : ∀ i : Fin m,
      ∫ τ : ℝ, Real.exp (-(A i * τ ^ 2 + B i * τ))
          ∂(gaussianReal 0 (1 / ((i : ℝ≥0) + 1) ^ 2)) =
        (√(1 + 2 * lam * δ))⁻¹ *
          Real.exp (δ * lam ^ 2 * ((i : ℝ) + 1) ^ 2 * x i ^ 2 / (2 * δ * lam + 1)) := by
    intro i
    have hvne : (1 / ((i : ℝ≥0) + 1) ^ 2 : ℝ≥0) ≠ 0 := by positivity
    rw [integral_exp_neg_quad_linear hvne (hA := hApos i)]
    have h1 : (1 : ℝ) + 2 * ((1 / ((i : ℝ≥0) + 1) ^ 2 : ℝ≥0) : ℝ) * A i = 1 + 2 * lam * δ := by
      rw [hvco]
      simp only [hAdef]
      have hne : ((i : ℝ) + 1) ^ 2 ≠ 0 := by positivity
      field_simp
    have hBsq : (B i) ^ 2 = lam ^ 2 * (2 * δ) * (((i : ℝ) + 1) ^ 2) ^ 2 * x i ^ 2 := by
      rw [hBdef, mul_pow, mul_pow, mul_pow,
        Real.sq_sqrt (by linarith : (0 : ℝ) ≤ 2 * δ)]
    have h2 : (B i) ^ 2 * ((1 / ((i : ℝ≥0) + 1) ^ 2 : ℝ≥0) : ℝ) /
        (2 * (1 + 2 * lam * δ)) =
        δ * lam ^ 2 * ((i : ℝ) + 1) ^ 2 * x i ^ 2 / (2 * δ * lam + 1) := by
      rw [hBsq, hvco]
      have hne : ((i : ℝ) + 1) ^ 2 ≠ 0 := by positivity
      have hd : 1 + 2 * lam * δ ≠ 0 := by positivity
      field_simp
      ring
    rw [h1, h2]
  have hval : ∫ ξ : Fin m → ℝ, Real.exp (-(lam * (∑ i : Fin m, ((i : ℝ) + 1) ^ 2 *
      (δ * ξ i ^ 2 + Real.sqrt (2 * δ) * x i * ξ i)))) ∂(gammaM m) =
      ∏ i : Fin m, (√(1 + 2 * lam * δ))⁻¹ *
        Real.exp (δ * lam ^ 2 * ((i : ℝ) + 1) ^ 2 * x i ^ 2 / (2 * δ * lam + 1)) := by
    conv_lhs => enter [2, ξ]; rw [hS_eq ξ]
    rw [integral_exp_sum_gammaM A B]
    exact Finset.prod_congr rfl fun i _ => hcoord i
  have hprod : (∏ i : Fin m, (√(1 + 2 * lam * δ))⁻¹ *
        Real.exp (δ * lam ^ 2 * ((i : ℝ) + 1) ^ 2 * x i ^ 2 / (2 * δ * lam + 1))) =
      (1 + 2 * lam * δ) ^ (-(m : ℝ) / 2) *
        Real.exp (∑ i : Fin m, δ * lam ^ 2 * ((i : ℝ) + 1) ^ 2 * x i ^ 2 / (2 * δ * lam + 1)) := by
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
      ← Real.exp_sum, inv_sqrt_pow _ (by positivity) m]
  have hint : Integrable (fun ξ : Fin m → ℝ => Real.exp (-(lam * (∑ i : Fin m,
      ((i : ℝ) + 1) ^ 2 * (δ * ξ i ^ 2 + Real.sqrt (2 * δ) * x i * ξ i))))) (gammaM m) := by
    have hfun : (fun ξ : Fin m → ℝ => Real.exp (-(lam * (∑ i : Fin m,
        ((i : ℝ) + 1) ^ 2 * (δ * ξ i ^ 2 + Real.sqrt (2 * δ) * x i * ξ i))))) =
        fun ξ => Real.exp (-(∑ i, (A i * ξ i ^ 2 + B i * ξ i))) := by
      funext ξ
      rw [hS_eq ξ]
    rw [hfun]
    exact integrable_exp_neg_quad_sum A B hApos
  calc accBar (rwmProposal m δ) (rwmAccept m) x
      = ∫⁻ ξ : Fin m → ℝ, ENNReal.ofReal (min 1 (Real.exp (-(∑ i : Fin m,
          ((i : ℝ) + 1) ^ 2 * (δ * ξ i ^ 2 + Real.sqrt (2 * δ) * x i * ξ i))))) ∂(gammaM m) := by
        rw [accBar_rwm]
        exact lintegral_congr fun ξ => rwmAccept_add_smul m δ hδ0 x ξ
    _ ≤ ∫⁻ ξ : Fin m → ℝ, ENNReal.ofReal (Real.exp (-(lam * (∑ i : Fin m,
          ((i : ℝ) + 1) ^ 2 * (δ * ξ i ^ 2 + Real.sqrt (2 * δ) * x i * ξ i))))) ∂(gammaM m) :=
        lintegral_mono fun ξ => ENNReal.ofReal_le_ofReal (min_one_exp_le hlam0 hlam1)
    _ = ENNReal.ofReal (∫ ξ : Fin m → ℝ, Real.exp (-(lam * (∑ i : Fin m,
          ((i : ℝ) + 1) ^ 2 * (δ * ξ i ^ 2 + Real.sqrt (2 * δ) * x i * ξ i)))) ∂(gammaM m)) :=
        (ofReal_integral_eq_lintegral_ofReal hint
          (Filter.Eventually.of_forall fun ξ => (Real.exp_pos _).le)).symm
    _ = ENNReal.ofReal ((1 + 2 * lam * δ) ^ (-(m : ℝ) / 2) *
          Real.exp (∑ i : Fin m, δ * lam ^ 2 * ((i : ℝ) + 1) ^ 2 * x i ^ 2 /
            (2 * δ * lam + 1))) := by
        rw [hval, hprod]

end MHSpectralGap.RWM

open MeasureTheory ProbabilityTheory MHSpectralGap.RWM in
/-- `MHSpectralGap.RWM.acceptance_bound`: the acceptance bound of Theorem 2.17, p. 16. -/
theorem solution (m : ℕ) (δ : ℝ) (hδ : 0 < δ) (lam : ℝ) (hlam : lam ∈ Set.Icc (0 : ℝ) 1)
    (x : Fin m → ℝ) :
    accBar (rwmProposal m δ) (rwmAccept m) x ≤
      ENNReal.ofReal ((1 + 2 * lam * δ) ^ (-(m : ℝ) / 2) *
        Real.exp (∑ i : Fin m, δ * lam ^ 2 * ((i : ℝ) + 1) ^ 2 * x i ^ 2 / (2 * δ * lam + 1))) :=
  MHSpectralGap.RWM.acceptance_bound_aux m δ hδ lam hlam x
