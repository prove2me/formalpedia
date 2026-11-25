-- Prove2me | solution 1 for GroundTheory.LocalField.addHaar_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T07:51:55.689963+00:00
-- url     : https://prove2.me/submissions/281775c3-b142-4ea9-9eb1-5d3af936bc4b

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_PadicLogSeries
import Definitions.Def_GroundTheory_LocalFields_Uniqueness
import Definitions.Def_GroundTheory_LocalFields_SeparableClosureValuation
import Definitions.Def_GroundTheory_LocalFields_LocalFourierHaar
import Theorems.Thm_GroundTheory_LocalField_measure_smul_eq_distribHaarChar
import Theorems.Thm_GroundTheory_LocalField_distribHaarChar_eq_modulus

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
theorem _root_.solution {a : K} (ha : a ≠ 0) (s : Set K) : μ (a • s) = modulus a * μ s := by
  rw [measure_smul_eq_distribHaarChar μ ha, distribHaarChar_eq_modulus, Units.val_mk0]
end GroundTheory.LocalField
