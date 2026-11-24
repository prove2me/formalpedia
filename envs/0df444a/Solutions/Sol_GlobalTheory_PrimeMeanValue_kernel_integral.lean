-- Prove2me | solution 1 for GlobalTheory.PrimeMeanValue.kernel_integral
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T19:46:35.6256+00:00
-- url     : https://prove2.me/submissions/fdb0f0a7-a1e9-4893-b2f2-7205355dd2a9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_ZerosDisc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_IntegralNormSqLp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_BrunTitchmarshExistsConstStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_PrimeMeanValueCharactersTwistIntegralLe
import Theorems.Thm_GlobalTheory_PrimeMeanValue_kernel_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology GlobalTheory.Lin
open scoped Classical
open GlobalTheory GlobalTheory.PrimeMeanValue
namespace GlobalTheory.PrimeMeanValue
theorem _root_.solution (n δ : ℝ) (hn : 0 < n) (hδ : 0 ≤ δ) :
    IntegrableOn (fun x : ℝ => if x < n ∧ n ≤ x * Real.exp δ then 1 / x else 0) (Set.Ioi 0) ∧
    ∫ x in Set.Ioi (0 : ℝ), (if x < n ∧ n ≤ x * Real.exp δ then 1 / x else 0) = δ := by
  simp_rw [kernel_eq]
  have he := Real.exp_pos δ
  have ha : 0 < n / Real.exp δ := by positivity
  have hle : n / Real.exp δ ≤ n := div_le_self hn.le (Real.one_le_exp hδ)
  have hsub : Set.Ico (n / Real.exp δ) n ⊆ Set.Ioi 0 := fun x hx => lt_of_lt_of_le ha hx.1
  constructor
  · refine Integrable.integrableOn ?_
    rw [integrable_indicator_iff measurableSet_Ico]
    refine IntegrableOn.mono_set ?_ Set.Ico_subset_Icc_self
    refine ContinuousOn.integrableOn_Icc ?_
    exact continuousOn_const.div continuousOn_id fun x hx => (lt_of_lt_of_le ha hx.1).ne'
  · rw [setIntegral_indicator measurableSet_Ico, Set.inter_eq_right.2 hsub,
      integral_Ico_eq_integral_Ioc, ← intervalIntegral.integral_of_le hle,
      integral_one_div_of_pos ha hn]
    rw [div_div_cancel₀ hn.ne', Real.log_exp]
end GlobalTheory.PrimeMeanValue
