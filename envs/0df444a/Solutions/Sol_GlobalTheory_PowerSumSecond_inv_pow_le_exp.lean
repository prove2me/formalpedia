-- Prove2me | solution 1 for GlobalTheory.PowerSumSecond.inv_pow_le_exp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T19:29:32.869286+00:00
-- url     : https://prove2.me/submissions/c41bd25c-9ab9-4fc9-874b-18473b8231dd

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ExistsProdAbsSubGeOnSegment
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ExistsInterpolationExteriorSmallCoeffsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_TuranSecondMainTheoremPowerSumsUnitCoefficients

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology
open GlobalTheory
open GlobalTheory.PowerSumSecond
namespace GlobalTheory.PowerSumSecond
theorem _root_.solution (N M : ℕ) (hN : 0 < N) (r : ℝ) (hr : 1 - (N : ℝ) / (2 * (M + N)) ≤ r) :
    1 ≤ r ^ M * Real.exp 1 ^ N := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hM' : (0 : ℝ) ≤ M := by positivity
  set u : ℝ := N / (2 * M + N) with hu
  have hu0 : 0 ≤ u := by positivity
  have h1 : (1 - (N : ℝ) / (2 * (M + N))) * (u + 1) = 1 := by
    rw [hu]; field_simp; ring
  have h2 : 1 ≤ r * Real.exp u := by
    have hs : 0 ≤ 1 - (N : ℝ) / (2 * (M + N)) := by
      rw [sub_nonneg, div_le_one (by positivity)]; linarith
    calc (1 : ℝ) = _ := h1.symm
      _ ≤ _ := mul_le_mul hr (Real.add_one_le_exp u) (by linarith) (hs.trans hr)
  have hr0 : 0 ≤ r := by
    have hs : 0 ≤ 1 - (N : ℝ) / (2 * (M + N)) := by
      rw [sub_nonneg, div_le_one (by positivity)]; linarith
    exact hs.trans hr
  have h3 : Real.exp u ^ M ≤ Real.exp 1 ^ N := by
    rw [← Real.exp_nat_mul, ← Real.exp_nat_mul]
    apply Real.exp_le_exp.2
    rw [hu, mul_one, ← mul_div_assoc, div_le_iff₀ (by positivity)]
    nlinarith [mul_nonneg hM' hN'.le]
  calc (1 : ℝ) ≤ (r * Real.exp u) ^ M := one_le_pow₀ h2
    _ = r ^ M * Real.exp u ^ M := mul_pow _ _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left h3 (by positivity)
end GlobalTheory.PowerSumSecond
