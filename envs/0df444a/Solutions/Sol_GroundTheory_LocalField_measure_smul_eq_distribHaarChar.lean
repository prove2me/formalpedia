-- Prove2me | solution 1 for GroundTheory.LocalField.measure_smul_eq_distribHaarChar
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T01:29:39.043478+00:00
-- url     : https://prove2.me/submissions/29d4af7a-766d-4e5c-9251-786a221ec747

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_PadicLogSeries
import Definitions.Def_GroundTheory_LocalFields_Uniqueness
import Definitions.Def_GroundTheory_LocalFields_SeparableClosureValuation
import Definitions.Def_GroundTheory_LocalFields_LocalFourierHaar

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
theorem _root_.solution {c : K} (hc : c ≠ 0) (s : Set K) :
    μ (c • s) = distribHaarChar K (Units.mk0 c hc) * μ s :=
  (distribHaarChar_mul μ (Units.mk0 c hc) s).symm
end GroundTheory.LocalField
