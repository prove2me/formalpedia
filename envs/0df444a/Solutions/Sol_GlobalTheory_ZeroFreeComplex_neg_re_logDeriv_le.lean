-- Prove2me | solution 1 for GlobalTheory.ZeroFreeComplex.neg_re_logDeriv_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T07:59:05.734794+00:00
-- url     : https://prove2.me/submissions/d2c46688-0848-4f96-9842-544f9ac48710

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_LogDerivativeBound
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_NegSumLogDerivNonneg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_LogDerivDirichletLFunctionLocalZeroSum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_NegReLogDerivPrincipalLFunctionLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_LFunctionConjEqZero
import Theorems.Thm_GlobalTheory_ZeroFreeComplex_one_le_order
import Theorems.Thm_GlobalTheory_ZeroFreeComplex_re_lt_one
import Theorems.Thm_GlobalTheory_LLocal_logDeriv_LFunction_local


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction MeasureTheory
open scoped ComplexConjugate
open GlobalTheory GlobalTheory.ZeroFreeComplex
namespace GlobalTheory.ZeroFreeComplex
theorem _root_.solution : ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
    χ ≠ 1 → ∀ (σ t : ℝ), 1 < σ → σ ≤ 2 → ∀ S : Finset ℂ,
    (∀ w ∈ S, ‖w - (3/2 + t * I)‖ ≤ 5/6 ∧ LFunction χ w = 0) →
    -(deriv (LFunction χ) (σ + t * I) / LFunction χ (σ + t * I)).re
      ≤ C * Real.log (q * (|t| + 2)) - ∑ w ∈ S, (1 / ((σ : ℂ) + t * I - w)).re := by
  obtain ⟨C, hC, hloc⟩ := GlobalTheory.LLocal.logDeriv_LFunction_local
  refine ⟨C, hC, fun q _ χ hχ σ t hσ hσ2 S hS => ?_⟩
  have hdist : ‖((σ : ℂ) + t * I) - (3/2 + t * I)‖ ≤ 2/3 := by
    rw [show ((σ : ℂ) + t * I) - (3/2 + t * I) = ((σ - 3/2 : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_real, Real.norm_eq_abs, abs_le]
    constructor <;> linarith
  have hre_s : ((σ : ℂ) + t * I).re = σ := by simp
  have hLs : LFunction χ ((σ : ℂ) + t * I) ≠ 0 :=
    LFunction_ne_zero_of_one_le_re χ (Or.inl hχ) (by rw [hre_s]; linarith)
  obtain ⟨hfin, hbound⟩ := hloc q χ hχ t ((σ : ℂ) + t * I) hdist hLs
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin] at hbound
  set A := deriv (LFunction χ) ((σ : ℂ) + t * I) / LFunction χ ((σ : ℂ) + t * I) with hA
  set B := ∑ w ∈ hfin.toFinset,
    (analyticOrderNatAt (LFunction χ) w : ℂ) / ((σ : ℂ) + t * I - w) with hB
  have hAB : -A.re ≤ C * Real.log (q * (|t| + 2)) - B.re := by
    have h := (Complex.abs_re_le_norm (A - B)).trans hbound
    rw [Complex.sub_re, abs_le] at h
    linarith [h.1]
  have hpos : ∀ w, LFunction χ w = 0 → 0 ≤ (1 / ((σ : ℂ) + t * I - w)).re := by
    intro w hw
    have hw1 := re_lt_one hχ hw
    have hz : 0 < ((σ : ℂ) + t * I - w).re := by simp; linarith
    rw [one_div, Complex.inv_re]
    exact div_nonneg hz.le (Complex.normSq_nonneg _)
  have hBre : B.re = ∑ w ∈ hfin.toFinset,
      (analyticOrderNatAt (LFunction χ) w : ℝ) * (1 / ((σ : ℂ) + t * I - w)).re := by
    rw [hB, Complex.re_sum]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [div_eq_mul_one_div, show ((analyticOrderNatAt (LFunction χ) w : ℕ) : ℂ) =
      ((analyticOrderNatAt (LFunction χ) w : ℝ) : ℂ) by push_cast; rfl, Complex.re_ofReal_mul]
  have hSsub : S ⊆ hfin.toFinset := by
    intro w hw
    rw [Set.Finite.mem_toFinset]
    exact hS w hw
  have hSle : ∑ w ∈ S, (1 / ((σ : ℂ) + t * I - w)).re ≤ B.re := by
    rw [hBre]
    calc ∑ w ∈ S, (1 / ((σ : ℂ) + t * I - w)).re
        ≤ ∑ w ∈ S, (analyticOrderNatAt (LFunction χ) w : ℝ) * (1 / ((σ : ℂ) + t * I - w)).re := by
          refine Finset.sum_le_sum fun w hw => ?_
          have hw0 := (hS w hw).2
          have h1 : (1 : ℝ) ≤ analyticOrderNatAt (LFunction χ) w := by
            exact_mod_cast one_le_order hχ hw0
          have h2 := hpos w hw0
          nlinarith
      _ ≤ ∑ w ∈ hfin.toFinset,
          (analyticOrderNatAt (LFunction χ) w : ℝ) * (1 / ((σ : ℂ) + t * I - w)).re := by
          refine Finset.sum_le_sum_of_subset_of_nonneg hSsub fun w hw _ => ?_
          rw [Set.Finite.mem_toFinset] at hw
          exact mul_nonneg (Nat.cast_nonneg _) (hpos w hw.2)
  linarith
end GlobalTheory.ZeroFreeComplex
