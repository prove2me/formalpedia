-- Prove2me | solution 1 for GroundTheory.LocalField.measure_valBall_eq_mul_succ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T07:05:33.582328+00:00
-- url     : https://prove2.me/submissions/f1e9c67a-022f-488f-9a58-adc5a1a4fc75

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_PadicLogSeries
import Definitions.Def_GroundTheory_LocalFields_Uniqueness
import Definitions.Def_GroundTheory_LocalFields_SeparableClosureValuation
import Definitions.Def_GroundTheory_LocalFields_LocalFourierHaar
import Theorems.Thm_GroundTheory_LocalField_measure_valBall_zero_eq_mul
import Theorems.Thm_GroundTheory_LocalField_measure_smul_eq_distribHaarChar

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.LocalField
open ValuativeRel MeasureTheory Measure Topology Filter TopologicalSpace
open scoped WithZero NNReal ENNReal Pointwise
variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable [MeasurableSpace K] [BorelSpace K]
variable (μ : Measure K) [μ.IsAddHaarMeasure]
namespace GroundTheory.LocalField
theorem _root_.solution (n : ℤ) :
    μ (valBall K n) = residueCard K * μ (valBall K (n + 1)) := by
  obtain ⟨c, hc, hcn⟩ := exists_ord_eq K n
  have h0 := measure_smul_eq_distribHaarChar μ hc (valBall K 0)
  have h1 := measure_smul_eq_distribHaarChar μ hc (valBall K 1)
  rw [smul_valBall hc, zero_add, hcn] at h0
  rw [smul_valBall hc, hcn, add_comm] at h1
  rw [h0, h1, measure_valBall_zero_eq_mul μ]
  ring
end GroundTheory.LocalField
