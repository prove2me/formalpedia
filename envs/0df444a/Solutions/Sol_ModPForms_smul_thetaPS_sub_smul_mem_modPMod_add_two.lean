-- Prove2me | solution 1 for ModPForms.smul_thetaPS_sub_smul_mem_modPMod_add_two
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/e6284931-4801-5b77-ac3d-8adf65af38b5

import Definitions.Def_CuspForm_ModPForms
import Definitions.Def_SwdAlgebra
import Theorems.Thm_ModularForm_exists_gamma0_coe_eq_serreDerivative
import Mathlib.NumberTheory.ModularForms.Derivative
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.E2.Transform
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.E2.MDifferentiable
import Mathlib.NumberTheory.ModularForms.QExpansion
import Mathlib.Analysis.Complex.UpperHalfPlane.Exp
import Mathlib.Analysis.Complex.TaylorSeries
import Mathlib.Analysis.Calculus.Deriv.Shift
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModPForms_smul_thetaPS_sub_smul_mem_modPMod_add_two

set_option autoImplicit false

set_option autoImplicit false

p2m_open "UpperHalfPlane~I"
open Complex Real Function
open ModularForm Derivative
open scoped ModularForm Manifold Topology

namespace SerreDerivative

section

variable {f : ℍ → ℂ} (hper : Periodic (f ∘ ofComplex) 1) (hhol : MDiff f)
  (hbdd : IsBoundedAtImInfty f)

include hper in

private lemma periodic_D_comp_ofComplex : Periodic ((D f) ∘ ofComplex) 1 := by
  intro z
  rcases le_or_gt z.im 0 with hz | hz
  · have hz1 : (z + 1).im ≤ 0 := by simp [Complex.add_im, hz]
    exact congrArg (D f) (ofComplex_apply_eq_of_im_nonpos hz1 hz)
  · have hz1 : (0 : ℝ) < (z + 1).im := by simp [Complex.add_im, hz]
    show (2 * π * I : ℂ)⁻¹ * deriv (f ∘ ofComplex) ↑(ofComplex (z + 1))
      = (2 * π * I : ℂ)⁻¹ * deriv (f ∘ ofComplex) ↑(ofComplex z)
    rw [ofComplex_apply_of_im_pos hz1, ofComplex_apply_of_im_pos hz,
      UpperHalfPlane.coe_mk, UpperHalfPlane.coe_mk]
    congr 1
    have heq : (fun x ↦ (f ∘ ofComplex) (x + 1)) = (f ∘ ofComplex) := funext hper
    calc deriv (f ∘ ofComplex) (z + 1)
          = deriv (fun x ↦ (f ∘ ofComplex) (x + 1)) z :=
            (deriv_comp_add_const (f ∘ ofComplex) 1 z).symm
      _ = deriv (f ∘ ofComplex) z := by rw [heq]

include hper hhol hbdd in

private lemma Df_eq_qParam_mul_derivCusp (τ : ℍ) :
    D f τ = Periodic.qParam 1 (τ : ℂ) * deriv (cuspFunction 1 f) (Periodic.qParam 1 (τ : ℂ)) := by
  set F := cuspFunction 1 f
  set q := Periodic.qParam 1 (τ : ℂ) with hqdef
  have hFdiff := differentiableOn_cuspFunction_ball one_pos hper hhol hbdd
  have hq1 : q ∈ Metric.ball (0 : ℂ) 1 := by
    rw [mem_ball_zero_iff, hqdef, Periodic.norm_qParam]
    have : (0 : ℝ) < 2 * π * τ.im := by positivity
    calc Real.exp (-2 * π * τ.im / 1) = Real.exp (-(2 * π * τ.im)) := by ring_nf
      _ < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hFd : DifferentiableAt ℂ F q :=
    (hFdiff q hq1).differentiableAt (Metric.isOpen_ball.mem_nhds hq1)
  have hcomp : (f ∘ ofComplex) =ᶠ[𝓝 (τ : ℂ)] F ∘ (Periodic.qParam 1) := by
    filter_upwards [isOpen_upperHalfPlaneSet.mem_nhds τ.2] with z hz
    show f (ofComplex z) = F (Periodic.qParam 1 z)
    rw [ofComplex_apply_of_im_pos hz]
    exact (eq_cuspFunction (⟨z, hz⟩ : ℍ) one_ne_zero hper).symm
  have hqd : HasDerivAt (Periodic.qParam 1) ((2 * π * I) * q) (τ : ℂ) := by
    have h1 : HasDerivAt (fun w ↦ (2 * π * I : ℂ) * w) (2 * π * I) (τ : ℂ) := by
      simpa using (hasDerivAt_id (τ : ℂ)).const_mul (2 * π * I : ℂ)
    refine ((h1.cexp).congr_of_eventuallyEq ?_).congr_deriv ?_
    · exact Filter.Eventually.of_forall fun w ↦ by simp [Periodic.qParam]
    · rw [hqdef]; simp only [Periodic.qParam, Complex.ofReal_one, div_one]; ring
  have hderiv : deriv (f ∘ ofComplex) (τ : ℂ) = deriv F q * ((2 * π * I) * q) := by
    rw [hcomp.deriv_eq, ← hqd.deriv]; exact deriv_comp _ hFd hqd.differentiableAt
  show (2 * π * I : ℂ)⁻¹ * deriv (f ∘ ofComplex) (τ : ℂ) = q * deriv F q
  rw [hderiv]; field_simp [Complex.two_pi_I_ne_zero]

include hper hhol hbdd in

private lemma isBoundedAtImInfty_D_one : IsBoundedAtImInfty (D f) := by
  set F := cuspFunction 1 f
  have hFdiff := differentiableOn_cuspFunction_ball one_pos hper hhol hbdd
  have hF'diff : DifferentiableOn ℂ (deriv F) (Metric.ball 0 1) :=
    (hFdiff.analyticOnNhd Metric.isOpen_ball).deriv.differentiableOn
  obtain ⟨C, hC⟩ : ∃ C, ∀ q ∈ Metric.closedBall (0 : ℂ) 2⁻¹, ‖deriv F q‖ ≤ C := by
    obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : ℂ) 2⁻¹).bddAbove_image
      ((hF'diff.mono (Metric.closedBall_subset_ball
        (show (2⁻¹ : ℝ) < 1 by norm_num))).continuousOn).norm
    exact ⟨C, fun q hq ↦ hC ⟨q, hq, rfl⟩⟩
  rw [isBoundedAtImInfty_iff]
  refine ⟨C, Real.log 2 / (2 * π), fun τ hτ ↦ ?_⟩
  have h2π : (0 : ℝ) < 2 * π := Real.two_pi_pos
  have hqτ : ‖Periodic.qParam 1 (τ : ℂ)‖ ≤ 2⁻¹ := by
    rw [Periodic.norm_qParam]
    have hle : Real.log 2 ≤ 2 * π * τ.im := by have := (div_le_iff₀ h2π).mp hτ; linarith
    calc Real.exp (-2 * π * τ.im / 1) = Real.exp (-(2 * π * τ.im)) := by ring_nf
      _ ≤ Real.exp (-Real.log 2) := Real.exp_le_exp.mpr (neg_le_neg hle)
      _ = 2⁻¹ := by rw [Real.exp_neg, Real.exp_log two_pos]
  calc ‖D f τ‖ = ‖Periodic.qParam 1 (τ : ℂ)‖ * ‖deriv F (Periodic.qParam 1 (τ : ℂ))‖ := by
        rw [Df_eq_qParam_mul_derivCusp hper hhol hbdd τ, norm_mul]
    _ ≤ 1 * C :=
        mul_le_mul (le_trans hqτ (by norm_num)) (hC _ (by rwa [Metric.mem_closedBall,
          dist_zero_right])) (norm_nonneg _) zero_le_one
    _ = C := one_mul C

include hper hhol hbdd in

private theorem analyticAt_cuspFunction_normalizedDeriv :
    AnalyticAt ℂ (cuspFunction 1 (D f)) 0 :=
  analyticAt_cuspFunction_zero one_pos (periodic_D_comp_ofComplex hper)
    (normalizedDerivOfComplex_mdifferentiable hhol) (isBoundedAtImInfty_D_one hper hhol hbdd)

include hper hhol hbdd in

private lemma hasSum_D_eq_theta_qExpansion (τ : ℍ) :
    HasSum (fun n : ℕ ↦ ((n : ℂ) * (qExpansion 1 f).coeff n) • (Periodic.qParam 1 (τ : ℂ)) ^ n)
      (D f τ) := by
  set F := cuspFunction 1 f
  set q := Periodic.qParam 1 (τ : ℂ) with hqdef
  have hFdiff := differentiableOn_cuspFunction_ball one_pos hper hhol hbdd
  have hF'diff : DifferentiableOn ℂ (deriv F) (Metric.ball 0 1) :=
    (hFdiff.analyticOnNhd Metric.isOpen_ball).deriv.differentiableOn
  have hq1 : q ∈ Metric.ball (0 : ℂ) 1 := by
    rw [mem_ball_zero_iff, hqdef, Periodic.norm_qParam]
    have : (0 : ℝ) < 2 * π * τ.im := by positivity
    calc Real.exp (-2 * π * τ.im / 1) = Real.exp (-(2 * π * τ.im)) := by ring_nf
      _ < 1 := Real.exp_lt_one_iff.mpr (by linarith)

  have hF'sum : HasSum
      (fun m : ℕ ↦ (((m + 1 : ℕ) : ℂ) * (qExpansion 1 f).coeff (m + 1)) • q ^ m)
      (deriv F q) := by
    have H := hasSum_taylorSeries_on_ball hF'diff hq1
    convert H using 1 <;> try with_reducible_and_instances rfl
    funext m
    rw [sub_zero, ← iteratedDeriv_succ', qExpansion_coeff]
    push_cast [Nat.factorial_succ]
    field_simp; ring

  have hqF' : HasSum
      (fun m : ℕ ↦ (((m + 1 : ℕ) : ℂ) * (qExpansion 1 f).coeff (m + 1)) • q ^ (m + 1))
      (q * deriv F q) := by
    have H := hF'sum.mul_left q
    convert H using 1 <;> try with_reducible_and_instances rfl
    funext m; rw [smul_eq_mul, smul_eq_mul, pow_succ]; ring
  have hfull : HasSum (fun n : ℕ ↦ ((n : ℂ) * (qExpansion 1 f).coeff n) • q ^ n)
      (q * deriv F q) := by
    have hshift := (hasSum_nat_add_iff
      (f := fun n : ℕ ↦ ((n : ℂ) * (qExpansion 1 f).coeff n) • q ^ n) 1).mp hqF'
    simpa using hshift
  rw [Df_eq_qParam_mul_derivCusp hper hhol hbdd τ]
  exact hfull

include hper hhol hbdd in

private theorem qExpansion_coeff_normalizedDeriv (n : ℕ) :
    (qExpansion 1 (D f)).coeff n = n * (qExpansion 1 f).coeff n := by
  have han := analyticAt_cuspFunction_normalizedDeriv hper hhol hbdd

  have h1 := (UpperHalfPlane.hasFPowerSeriesOnBall_cuspFunction (f := D f)
    (c := fun m ↦ (m : ℂ) * (qExpansion 1 f).coeff m) one_pos han
    (fun τ ↦ hasSum_D_eq_theta_qExpansion hper hhol hbdd τ)).hasFPowerSeriesAt

  have h2 : HasFPowerSeriesAt (cuspFunction 1 (D f))
      (FormalMultilinearSeries.ofScalars ℂ fun m ↦ (qExpansion 1 (D f)).coeff m) 0 := by
    simpa [UpperHalfPlane.qExpansion_coeff, div_eq_mul_inv, mul_comm] using han.hasFPowerSeriesAt
  have h3 := congr_arg (FormalMultilinearSeries.coeff · n) (h1.eq_formalMultilinearSeries h2)
  simpa [FormalMultilinearSeries.coeff_ofScalars] using h3.symm

end

end SerreDerivative

section

p2m_open "UpperHalfPlane~I"
p2m_open "Complex Function.Complex Function ModularForm CongruenceSubgroup Derivative EisensteinSeries"
open scoped MatrixGroups ModularForm Manifold Topology ArithmeticFunction.sigma Real

namespace SerreDerivative

private def e2c : ℕ → ℤ
  | 0 => 1
  | (n + 1) => -24 * σ 1 (n + 1)

private lemma E2_T_periodic (τ : ℍ) : E2 ((1 : ℝ) +ᵥ τ) = E2 τ := by
  have hsl : (E2 ∣[(2 : ℤ)] ModularGroup.T) = E2 := by
    rw [E2_slash_action]; simp [D2_T]
  have happ := congrFun hsl τ
  rw [SL_slash_apply, modular_T_smul] at happ
  simp only [ModularGroup.denom_apply, ModularGroup.T, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one,
    Int.cast_zero, zero_mul, Int.cast_one, zero_add, one_zpow, mul_one] at happ
  exact happ

private lemma periodic_E2_comp_ofComplex : Periodic (E2 ∘ ofComplex) 1 := by
  intro z
  rcases le_or_gt z.im 0 with hz | hz
  · have hz1 : (z + 1).im ≤ 0 := by simp [Complex.add_im, hz]
    exact congrArg E2 (ofComplex_apply_eq_of_im_nonpos hz1 hz)
  · have hz1 : (0 : ℝ) < (z + 1).im := by simp [Complex.add_im, hz]
    show E2 (ofComplex (z + 1)) = E2 (ofComplex z)
    rw [ofComplex_apply_of_im_pos hz1, ofComplex_apply_of_im_pos hz]
    have heq : (⟨z + 1, hz1⟩ : ℍ) = (1 : ℝ) +ᵥ (⟨z, hz⟩ : ℍ) := by
      refine UpperHalfPlane.ext_iff.mpr ?_
      simp only [coe_vadd, Complex.ofReal_one]
      ring
    rw [heq]; exact E2_T_periodic ⟨z, hz⟩

private theorem isBoundedAtImInfty_E2 : IsBoundedAtImInfty E2 := by
  rw [UpperHalfPlane.isBoundedAtImInfty_iff]

  set r₀ : ℝ := Real.exp (-Real.pi) with hr₀
  have hr₀0 : 0 ≤ r₀ := (Real.exp_pos _).le
  have hr₀1 : ‖r₀‖ < 1 := by
    rw [Real.norm_of_nonneg hr₀0, hr₀, Real.exp_lt_one_iff, neg_lt_zero]
    exact Real.pi_pos
  have hg : Summable fun n : ℕ+ => ((n : ℕ) : ℝ) ^ 2 * r₀ ^ (n : ℕ) :=
    (summable_pow_mul_geometric_of_norm_lt_one 2 hr₀1).comp_injective PNat.coe_injective
  refine ⟨1 + 24 * ∑' n : ℕ+, ((n : ℕ) : ℝ) ^ 2 * r₀ ^ (n : ℕ), 1 / 2, fun z hz => ?_⟩

  have hq : ‖cexp (2 * Real.pi * I * (z : ℂ))‖ ≤ r₀ := by
    have h := Function.Periodic.norm_qParam_le_of_one_half_le_im (ξ := (z : ℂ)) (by simpa using hz)
    simpa [Function.Periodic.qParam] using h

  have hle : ∀ n : ℕ+, ‖(σ 1 n : ℂ) * cexp (2 * Real.pi * I * (z : ℂ)) ^ (n : ℕ)‖ ≤
      ((n : ℕ) : ℝ) ^ 2 * r₀ ^ (n : ℕ) := by
    intro n
    rw [norm_mul, norm_pow, Complex.norm_natCast]
    gcongr
    · exact_mod_cast ArithmeticFunction.sigma_le_pow_succ 1 n
  have hf : Summable fun n : ℕ+ => ‖(σ 1 n : ℂ) * cexp (2 * Real.pi * I * (z : ℂ)) ^ (n : ℕ)‖ :=
    Summable.of_nonneg_of_le (fun n => norm_nonneg _) hle hg
  rw [E2_eq_tsum_cexp z]
  calc ‖1 - 24 * ∑' n : ℕ+, (σ 1 n : ℂ) * cexp (2 * Real.pi * I * (z : ℂ)) ^ (n : ℕ)‖
      ≤ ‖(1 : ℂ)‖ + ‖24 * ∑' n : ℕ+, (σ 1 n : ℂ) * cexp (2 * Real.pi * I * (z : ℂ)) ^ (n : ℕ)‖ :=
        norm_sub_le _ _
    _ = 1 + 24 * ‖∑' n : ℕ+, (σ 1 n : ℂ) * cexp (2 * Real.pi * I * (z : ℂ)) ^ (n : ℕ)‖ := by
        rw [norm_one, norm_mul, Complex.norm_ofNat]
    _ ≤ 1 + 24 * ∑' n : ℕ+, ‖(σ 1 n : ℂ) * cexp (2 * Real.pi * I * (z : ℂ)) ^ (n : ℕ)‖ := by
        gcongr
        exact norm_tsum_le_tsum_norm hf
    _ ≤ 1 + 24 * ∑' n : ℕ+, ((n : ℕ) : ℝ) ^ 2 * r₀ ^ (n : ℕ) := by
        have h := hf.tsum_le_tsum hle hg
        linarith

private lemma analyticAt_cuspFunction_E2 : AnalyticAt ℂ (cuspFunction 1 E2) 0 :=
  analyticAt_cuspFunction_zero one_pos periodic_E2_comp_ofComplex E2_mdifferentiable
    isBoundedAtImInfty_E2

private lemma hasSum_E2 (τ : ℍ) :
    HasSum (fun n : ℕ ↦ (e2c n : ℂ) • (Periodic.qParam 1 (τ : ℂ)) ^ n) (E2 τ) := by
  set q := Periodic.qParam 1 (τ : ℂ) with hqdef
  have hq1 : ‖q‖ < 1 := by
    rw [hqdef, Periodic.norm_qParam]
    have : (0 : ℝ) < 2 * π * τ.im := by positivity
    calc Real.exp (-2 * π * τ.im / 1) = Real.exp (-(2 * π * τ.im)) := by ring_nf
      _ < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hg : Summable fun n : ℕ+ => ((n : ℕ) : ℝ) ^ 2 * ‖q‖ ^ (n : ℕ) := by
    have hq1' : ‖(‖q‖ : ℝ)‖ < 1 := by simpa using hq1
    exact (summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 2 hq1').comp_injective PNat.coe_injective
  have hle : ∀ n : ℕ+, ‖(σ 1 n : ℂ) * q ^ (n : ℕ)‖ ≤ ((n : ℕ) : ℝ) ^ 2 * ‖q‖ ^ (n : ℕ) := by
    intro n
    rw [norm_mul, norm_pow, Complex.norm_natCast]
    gcongr
    exact_mod_cast ArithmeticFunction.sigma_le_pow_succ 1 n
  have hsum : Summable fun n : ℕ+ => (σ 1 n : ℂ) * q ^ (n : ℕ) :=
    .of_norm (Summable.of_nonneg_of_le (fun n => norm_nonneg _) hle hg)
  have hqeq : q = cexp (2 * ↑Real.pi * I * ↑τ) := by
    rw [hqdef, Periodic.qParam]; congr 1; push_cast; ring
  have hE2 : E2 τ = 1 - 24 * ∑' n : ℕ+, (σ 1 n : ℂ) * q ^ (n : ℕ) := by
    rw [hqeq]; exact E2_eq_tsum_cexp τ
  rw [hE2]
  have hre : HasSum (fun m : ℕ => (σ 1 (m + 1) : ℂ) * q ^ (m + 1))
      (∑' n : ℕ+, (σ 1 n : ℂ) * q ^ (n : ℕ)) := by
    have h0 := Equiv.pnatEquivNat.symm.hasSum_iff.mpr hsum.hasSum
    convert h0 using 1 <;> try with_reducible_and_instances rfl
    all_goals first | rfl | (funext m; simp)
  have htar : HasSum (fun m : ℕ => ((e2c (m + 1) : ℤ) : ℂ) • q ^ (m + 1))
      (- 24 * ∑' n : ℕ+, (σ 1 n : ℂ) * q ^ (n : ℕ)) := by
    have h0 := hre.mul_left (-24 : ℂ)
    convert h0 using 1 <;> try with_reducible_and_instances rfl
    funext m; simp only [e2c, smul_eq_mul]; push_cast; ring
  have hfull := (hasSum_nat_add_iff (f := fun n : ℕ => ((e2c n : ℤ) : ℂ) • q ^ n) 1).mp htar
  simp only [Finset.range_one, Finset.sum_singleton, pow_zero, smul_eq_mul, mul_one] at hfull
  convert hfull using 1 <;> try with_reducible_and_instances rfl
  all_goals first | (simp only [e2c, Int.cast_one]; ring) | (simp only [e2c, Int.cast_one]) | ring

private theorem qExpansion_E2_coeff (n : ℕ) :
    (qExpansion 1 EisensteinSeries.E2).coeff n = ((e2c n : ℤ) : ℂ) := by
  have han := analyticAt_cuspFunction_E2
  have h1 := (UpperHalfPlane.hasFPowerSeriesOnBall_cuspFunction (f := E2)
    (c := fun m ↦ ((e2c m : ℤ) : ℂ)) one_pos han (fun τ ↦ hasSum_E2 τ)).hasFPowerSeriesAt
  have h2 : HasFPowerSeriesAt (cuspFunction 1 E2)
      (FormalMultilinearSeries.ofScalars ℂ fun m ↦ (qExpansion 1 E2).coeff m) 0 := by
    simpa [qExpansion_coeff, div_eq_mul_inv, mul_comm] using han.hasFPowerSeriesAt
  have h3 := congr_arg (FormalMultilinearSeries.coeff · n) (h1.eq_formalMultilinearSeries h2)
  simpa [FormalMultilinearSeries.coeff_ofScalars] using h3.symm

end SerreDerivative

end

section

p2m_open "UpperHalfPlane~I"
p2m_open "Complex Function.Complex Function ModularForm CongruenceSubgroup Derivative EisensteinSeries"
open scoped MatrixGroups ModularForm Manifold Topology ArithmeticFunction.sigma Real

namespace SerreDerivative

variable {N' : ℕ} {k : ℤ}

variable {N' : ℕ} {k : ℤ}

private lemma T_mem_Gamma0 (N : ℕ) : ModularGroup.T ∈ Gamma0 N := by
  simp [Gamma0_mem, ModularGroup.coe_T]

private lemma one_mem_strictPeriods_Gamma0 (N : ℕ) :
    (1 : ℝ) ∈ ((Gamma0 N : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by
  rw [Subgroup.strictPeriods_eq_zmultiples_one_of_T_mem (T_mem_Gamma0 N)]
  exact AddSubgroup.mem_zmultiples 1

private lemma analyticAt_mf (f : ModularForm (Gamma0 N') k) : AnalyticAt ℂ (cuspFunction 1 ⇑f) 0 :=
  ModularFormClass.analyticAt_cuspFunction_zero f one_pos (one_mem_strictPeriods_Gamma0 N')

private lemma periodic_mf (f : ModularForm (Gamma0 N') k) : Periodic (⇑f ∘ ofComplex) 1 :=
  SlashInvariantFormClass.periodic_comp_ofComplex f (one_mem_strictPeriods_Gamma0 N')

private lemma bdd_mf (f : ModularForm (Gamma0 N') k) : IsBoundedAtImInfty ⇑f :=
  haveI : Fact (IsCusp OnePoint.infty ((Gamma0 N' : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))) :=
    ⟨Subgroup.isCusp_of_mem_strictPeriods one_pos (one_mem_strictPeriods_Gamma0 N')⟩
  ModularFormClass.bdd_at_infty f

private lemma qCoeff_eq (f : ℍ → ℂ) (n : ℕ) : ModularFormClass.qCoeff f n = (qExpansion 1 f).coeff n := rfl

private def serreCoeff (k : ℤ) (a : ℕ → ℤ) (n : ℕ) : ℤ :=
  12 * n * a n - k * ∑ x ∈ Finset.HasAntidiagonal.antidiagonal n, e2c x.1 * a x.2

private theorem exists_form_qCoeff_serreCoeff [NeZero N']
    (f : ModularForm (Gamma0 N') k) (a : ℕ → ℤ)
    (ha : ∀ n, ModularFormClass.qCoeff f n = (a n : ℂ)) :
    ∃ g : ModularForm (Gamma0 N') (k + 2),
      ∀ n, ModularFormClass.qCoeff g n = (serreCoeff k a n : ℂ) := by
  obtain ⟨gf, hgf⟩ := ModularForm.exists_gamma0_coe_eq_serreDerivative N' k f
  refine ⟨(12 : ℂ) • gf, fun n => ?_⟩
  have hcoe : (⇑((12 : ℂ) • gf) : ℍ → ℂ) =
      (12 : ℂ) • D ⇑f - (k : ℂ) • (EisensteinSeries.E2 * ⇑f) := by
    ext z
    simp only [ModularForm.IsGLPos.coe_smul, Pi.smul_apply, hgf, serreDerivative_apply,
      Pi.sub_apply, Pi.mul_apply, smul_eq_mul]
    ring
  have hDf := qExpansion_coeff_normalizedDeriv (periodic_mf f) (ModularFormClass.holo f) (bdd_mf f)
  have hDf_an := analyticAt_cuspFunction_normalizedDeriv (periodic_mf f) (ModularFormClass.holo f) (bdd_mf f)
  have hf_an := analyticAt_mf f
  have hE2_an := analyticAt_cuspFunction_E2
  have hprod_an : AnalyticAt ℂ (cuspFunction 1 (EisensteinSeries.E2 * ⇑f)) 0 := by
    rw [cuspFunction_mul hE2_an.continuousAt hf_an.continuousAt]
    exact hE2_an.mul hf_an
  have hDfs_an : AnalyticAt ℂ (cuspFunction 1 ((12 : ℂ) • D ⇑f)) 0 := by
    rw [cuspFunction_smul hDf_an.continuousAt]
    exact hDf_an.const_smul
  have hprods_an : AnalyticAt ℂ (cuspFunction 1 ((k : ℂ) • (EisensteinSeries.E2 * ⇑f))) 0 := by
    rw [cuspFunction_smul hprod_an.continuousAt]
    exact hprod_an.const_smul
  have hq : qExpansion 1 (⇑((12 : ℂ) • gf) : ℍ → ℂ) =
      (12 : ℂ) • qExpansion 1 (D ⇑f) -
        (k : ℂ) • (qExpansion 1 EisensteinSeries.E2 * qExpansion 1 ⇑f) := by
    rw [hcoe, qExpansion_sub hDfs_an hprods_an, qExpansion_smul hDf_an, qExpansion_smul hprod_an,
      qExpansion_mul hE2_an hf_an]
  have ha' : ∀ i, (qExpansion 1 ⇑f).coeff i = (a i : ℂ) := ha
  rw [qCoeff_eq, hq, map_sub, map_smul, map_smul, PowerSeries.coeff_mul, smul_eq_mul, smul_eq_mul]
  simp only [hDf, ha', qExpansion_E2_coeff, serreCoeff]
  push_cast
  ring

private lemma coeff_thetaPS' {F : Type} [Field F] (φ : PowerSeries F) (n : ℕ) :
    PowerSeries.coeff n (ModPForms.thetaPS φ) = (n : F) * PowerSeries.coeff n φ := by
  simp [ModPForms.thetaPS]

private lemma thetaPS_add' {F : Type} [Field F] (φ ψ : PowerSeries F) :
    ModPForms.thetaPS (φ + ψ) = ModPForms.thetaPS φ + ModPForms.thetaPS ψ := by
  ext n; simp [coeff_thetaPS', mul_add]

private lemma thetaPS_smul' {F : Type} [Field F] (c : F) (φ : PowerSeries F) :
    ModPForms.thetaPS (c • φ) = c • ModPForms.thetaPS φ := by
  ext n; simp [coeff_thetaPS']; ring

private lemma thetaPS_zero' {F : Type} [Field F] : ModPForms.thetaPS (0 : PowerSeries F) = 0 := by
  ext n; simp [coeff_thetaPS']

private lemma coeff_qP (F : Type) [Field F] (i : ℕ) :
    PowerSeries.coeff i (SwdAlgebra.qP F) = ((e2c i : ℤ) : F) := by
  have hz : (PowerSeries.mk fun n => if n = 0 then 1 else
      -24 * ∑ d ∈ n.divisors, (d : ℤ)).coeff i = e2c i := by
    cases i with
    | zero => simp [e2c]
    | succ m =>
        simp [e2c, ArithmeticFunction.sigma_one_apply]
  simp only [SwdAlgebra.qP, PowerSeries.coeff_map, hz]
  exact congrFun Int.coe_castRingHom (e2c i)

private theorem serreN (N' : ℕ) [NeZero N'] (F : Type) [Field F] (k : ℤ) (φ : PowerSeries F)
    (hφ : φ ∈ ModPForms.modPMod N' k F) :
    (12 : F) • ModPForms.thetaPS φ - (k : F) • (SwdAlgebra.qP F * φ) ∈
      ModPForms.modPMod N' (k + 2) F := by
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hφ
  · rintro _ ⟨f, a, ha, rfl⟩
    obtain ⟨g, hge⟩ := exists_form_qCoeff_serreCoeff f a ha
    have hmem : (PowerSeries.mk fun n => ((serreCoeff k a n : ℤ) : F)) ∈
        ModPForms.modPMod N' (k + 2) F :=
      Submodule.subset_span ⟨g, serreCoeff k a, hge, rfl⟩
    have hiden : (12 : F) • ModPForms.thetaPS (PowerSeries.mk fun n => ((a n : ℤ) : F)) -
        (k : F) • (SwdAlgebra.qP F * PowerSeries.mk fun n => ((a n : ℤ) : F)) =
        PowerSeries.mk fun n => ((serreCoeff k a n : ℤ) : F) := by
      ext n
      simp only [map_sub, map_smul, coeff_thetaPS', PowerSeries.coeff_mul, coeff_qP,
        PowerSeries.coeff_mk, serreCoeff, smul_eq_mul]
      push_cast
      ring
    rw [hiden]
    exact hmem
  · have h0 : (12 : F) • ModPForms.thetaPS (0 : PowerSeries F) -
        (k : F) • (SwdAlgebra.qP F * 0) = 0 := by
      rw [thetaPS_zero', mul_zero, smul_zero, smul_zero, sub_zero]
    rw [h0]; exact Submodule.zero_mem _
  · intro x y _ _ hx hy
    have hxy : (12 : F) • ModPForms.thetaPS (x + y) - (k : F) • (SwdAlgebra.qP F * (x + y)) =
        ((12 : F) • ModPForms.thetaPS x - (k : F) • (SwdAlgebra.qP F * x)) +
          ((12 : F) • ModPForms.thetaPS y - (k : F) • (SwdAlgebra.qP F * y)) := by
      rw [thetaPS_add', mul_add, smul_add, smul_add, sub_add_sub_comm]
    rw [hxy]; exact Submodule.add_mem _ hx hy
  · intro c x _ hx
    have hcx : (12 : F) • ModPForms.thetaPS (c • x) - (k : F) • (SwdAlgebra.qP F * (c • x)) =
        c • ((12 : F) • ModPForms.thetaPS x - (k : F) • (SwdAlgebra.qP F * x)) := by
      rw [thetaPS_smul', mul_smul_comm, smul_comm (12 : F) c, smul_comm (k : F) c, smul_sub]
    rw [hcx]; exact Submodule.smul_mem _ c hx

end SerreDerivative

end

theorem solution (N' : ℕ) [NeZero N'] (F : Type) [Field F] (k : ℤ)
    (φ : PowerSeries F) (hφ : φ ∈ ModPForms.modPMod N' k F) :
    (12 : F) • ModPForms.thetaPS φ - (k : F) • (SwdAlgebra.qP F * φ) ∈ ModPForms.modPMod N' (k + 2) F :=
  SerreDerivative.serreN N' F k φ hφ

end S_ModPForms_smul_thetaPS_sub_smul_mem_modPMod_add_two
end P2MW
export P2MW.S_ModPForms_smul_thetaPS_sub_smul_mem_modPMod_add_two (solution)
