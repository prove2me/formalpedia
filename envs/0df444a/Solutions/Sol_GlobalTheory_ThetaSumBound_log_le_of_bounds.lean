-- Prove2me | solution 1 for GlobalTheory.ThetaSumBound.log_le_of_bounds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T03:38:48.299605+00:00
-- url     : https://prove2.me/submissions/b659e0d9-e689-44eb-a19a-fcfee33e9bdb

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_TorusAtData
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainPointBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_ModerateCoefficientPositivity
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_TorusAtPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_TorusAtDataPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_SplitC
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ExistsThetaRunParametersUniformTorusStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_FirstMinimumSqMulIInfHeightLeCard

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.I2
open GlobalTheory GlobalTheory.ThetaSumBound
namespace GlobalTheory.ThetaSumBound
theorem _root_.solution {K S la th c k B p3 p1 f t : ℝ} (hK : 0 < K) (hS : 0 < S) (hla : 0 < la)
    (hth : 0 < th) (hc : 0 < c) (hk : 0 < k) (hB : 0 ≤ B) (hf : 0 < f) (ht : la ^ 2 * t ≤ f)
    (h1 : la < th → S ≤ K * (Real.exp p3 * (k * (c / la ^ 2)) ^ B *
      Real.exp (-(Real.pi * (c / la ^ 2) / 5 ^ 4))) ^ 2)
    (h2 : th ≤ la → S ≤ K * Real.exp p1 ^ 2) :
    Real.log S ≤ (Real.log K + 2 * |p3| + 2 * B * |Real.log (k * c)| + 2 * |p1| +
      2 * Real.pi * c / (5 ^ 4 * th ^ 2)) + 4 * B * Real.log (1 + 1 / la) -
      2 * Real.pi * c / (5 ^ 4 * f) * t := by
  have hpi := Real.pi_pos
  have hl0 : 0 ≤ Real.log (1 + 1 / la) := Real.log_nonneg (by have := one_div_pos.2 hla; linarith)
  have hd : 2 * Real.pi * c / (5 ^ 4 * f) * t ≤ 2 * Real.pi * c / (5 ^ 4 * la ^ 2) := by
    have : t ≤ f / la ^ 2 := by rw [le_div_iff₀ (by positivity)]; linarith
    calc 2 * Real.pi * c / (5 ^ 4 * f) * t ≤ 2 * Real.pi * c / (5 ^ 4 * f) * (f / la ^ 2) :=
          mul_le_mul_of_nonneg_left this (by positivity)
      _ = _ := by field_simp
  have hth0 : 0 ≤ 2 * Real.pi * c / (5 ^ 4 * th ^ 2) := by positivity
  have a3 := abs_nonneg p3
  have a1 := abs_nonneg p1
  have ak : 0 ≤ B * |Real.log (k * c)| := by positivity
  have aB := mul_nonneg hB hl0
  rcases lt_or_ge la th with h | h
  · have h3 := Real.log_le_log hS (h1 h)
    rw [Real.log_mul hK.ne' (by positivity), Real.log_pow, Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity), Real.log_exp, Real.log_exp,
      Real.log_rpow (by positivity)] at h3
    have h4 : Real.log (k * (c / la ^ 2)) ≤ |Real.log (k * c)| + 2 * Real.log (1 + 1 / la) := by
      have e : k * (c / la ^ 2) = (k * c) * (1 / la) ^ 2 := by field_simp
      rw [e, Real.log_mul (by positivity) (by positivity), Real.log_pow]
      have := Real.log_le_log (one_div_pos.2 hla) (show 1 / la ≤ 1 + 1 / la by linarith)
      have := le_abs_self (Real.log (k * c))
      push_cast
      linarith
    have h5 := mul_le_mul_of_nonneg_left h4 hB
    have e : 2 * Real.pi * c / (5 ^ 4 * la ^ 2) = 2 * (Real.pi * (c / la ^ 2) / 5 ^ 4) := by
      field_simp
    have := le_abs_self p3
    push_cast at h3
    linarith
  · have h3 := Real.log_le_log hS (h2 h)
    rw [Real.log_mul hK.ne' (by positivity), Real.log_pow, Real.log_exp] at h3
    have h4 : 2 * Real.pi * c / (5 ^ 4 * la ^ 2) ≤ 2 * Real.pi * c / (5 ^ 4 * th ^ 2) := by
      gcongr
    have := le_abs_self p1
    push_cast at h3
    linarith
end GlobalTheory.ThetaSumBound
