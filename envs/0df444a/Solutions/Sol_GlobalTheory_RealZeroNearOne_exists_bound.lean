-- Prove2me | solution 1 for GlobalTheory.RealZeroNearOne.exists_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T07:15:48.892491+00:00
-- url     : https://prove2.me/submissions/fe0d584a-600d-421a-a65e-4a4c91d16433

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_LogDerivDirichletLFunctionLocalZeroSumStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_NegReLogDerivPrincipalLFunctionLeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_NegSumLogDerivNonneg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_OrderNeTop
import Theorems.Thm_GlobalTheory_RealZeroNearOne_re_lt_one
import Theorems.Thm_GlobalTheory_T_logDeriv_dirichletLFunction_local_zero_sum


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction MeasureTheory
open GlobalTheory GlobalTheory.RealZeroNearOne
namespace GlobalTheory.RealZeroNearOne
theorem _root_.solution : ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
    χ ≠ 1 → ∀ σ : ℝ, 1 < σ → σ ≤ 2 → ∀ T : Finset ℝ,
    (∀ β ∈ T, 2 / 3 ≤ β ∧ LFunction χ β = 0) →
    -(deriv (LFunction χ) σ / LFunction χ σ).re ≤ C * Real.log (2 * q)
      - ∑ β ∈ T, (analyticOrderNatAt (LFunction χ) β : ℝ) / (σ - β) := by
  obtain ⟨C, hC, hb⟩ := GlobalTheory.T.logDeriv_dirichletLFunction_local_zero_sum
  refine ⟨C, hC, fun q _ χ hχ σ hσ hσ2 T hT => ?_⟩
  have hs : ‖(σ : ℂ) - (3 / 2 + ((0 : ℝ) : ℂ) * I)‖ ≤ 2 / 3 := by
    have e : (σ : ℂ) - (3 / 2 + ((0 : ℝ) : ℂ) * I) = ((σ - 3 / 2 : ℝ) : ℂ) := by push_cast; ring
    rw [e, Complex.norm_real, Real.norm_eq_abs, abs_le]
    constructor <;> linarith
  have hLσ : LFunction χ σ ≠ 0 :=
    LFunction_ne_zero_of_one_le_re χ (.inl hχ) (by rw [Complex.ofReal_re]; linarith)
  obtain ⟨hfin, hbd⟩ := hb q χ hχ 0 σ hs hLσ
  set f : ℂ → ℂ := fun w => (analyticOrderNatAt (LFunction χ) w : ℂ) / (σ - w) with hf
  set D := deriv (LFunction χ) σ / LFunction χ σ with hD
  have hlog : Real.log (q * (|(0 : ℝ)| + 2)) = Real.log (2 * q) := by
    congr 1; rw [abs_zero, zero_add, mul_comm]
  rw [hlog] at hbd
  have hre := (Complex.abs_re_le_norm _).trans hbd
  rw [Complex.sub_re] at hre
  have hsub : T.map ⟨((↑) : ℝ → ℂ), Complex.ofReal_injective⟩ ⊆ hfin.toFinset := by
    intro w hw
    rw [Finset.mem_map] at hw
    obtain ⟨β, hβ, rfl⟩ := hw
    obtain ⟨hβ1, hβ2⟩ := hT β hβ
    have hβlt : β < 1 := by simpa using re_lt_one hχ hβ2
    rw [Set.Finite.mem_toFinset]
    refine ⟨?_, hβ2⟩
    have e : (β : ℂ) - (3 / 2 + ((0 : ℝ) : ℂ) * I) = ((β - 3 / 2 : ℝ) : ℂ) := by push_cast; ring
    simp only [Function.Embedding.coeFn_mk]
    rw [e, Complex.norm_real, Real.norm_eq_abs, abs_le]
    constructor <;> linarith
  have hST : ∑ β ∈ T, (analyticOrderNatAt (LFunction χ) β : ℝ) / (σ - β) ≤
      (∑ᶠ w ∈ {w : ℂ | ‖w - (3 / 2 + ((0 : ℝ) : ℂ) * I)‖ ≤ 5 / 6 ∧ LFunction χ w = 0}, f w).re := by
    rw [finsum_mem_eq_finite_toFinset_sum _ hfin, Complex.re_sum]
    calc ∑ β ∈ T, (analyticOrderNatAt (LFunction χ) β : ℝ) / (σ - β)
        = ∑ w ∈ T.map ⟨((↑) : ℝ → ℂ), Complex.ofReal_injective⟩, (f w).re := by
          rw [Finset.sum_map]
          refine Finset.sum_congr rfl fun β _ => ?_
          simp only [Function.Embedding.coeFn_mk, hf]
          rw [← Complex.ofReal_natCast, ← Complex.ofReal_sub, ← Complex.ofReal_div,
            Complex.ofReal_re]
      _ ≤ ∑ w ∈ hfin.toFinset, (f w).re := by
          refine Finset.sum_le_sum_of_subset_of_nonneg hsub fun w hw _ => ?_
          rw [Set.Finite.mem_toFinset] at hw
          have hwre : w.re < 1 := re_lt_one hχ hw.2
          simp only [hf]
          rw [div_eq_mul_inv, ← Complex.ofReal_natCast, Complex.re_ofReal_mul, Complex.inv_re]
          refine mul_nonneg (Nat.cast_nonneg _) (div_nonneg ?_ (Complex.normSq_nonneg _))
          rw [Complex.sub_re, Complex.ofReal_re]
          linarith
  have := neg_abs_le (D.re - (∑ᶠ w ∈ {w : ℂ | ‖w - (3 / 2 + ((0 : ℝ) : ℂ) * I)‖ ≤ 5 / 6 ∧
    LFunction χ w = 0}, f w).re)
  linarith
end GlobalTheory.RealZeroNearOne
