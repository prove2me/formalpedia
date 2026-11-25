-- Prove2me | solution 1 for MassDataLevelSSteps.toReal_eq_relIndex_mul_of_open
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:40:57.229799+00:00
-- url     : https://prove2.me/submissions/56f3ccfa-0cdc-4b02-8a39-6a19859a0a29

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelStructures_HaarIdx
import Theorems.Thm_MassDataLevelSSteps_toReal_eq_relIndex_mul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MassDataLevelSSteps
open MeasureTheory
namespace MassDataLevelSSteps
theorem _root_.solution {G : Type} [Group G] [TopologicalSpace G] [ContinuousMul G]
    [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsMulLeftInvariant] [μ.IsOpenPosMeasure]
    (H K : Subgroup G) (hle : H ≤ K) (hH : IsOpen (H : Set G)) :
    (μ K).toReal = (H.relIndex K : ℝ) * (μ H).toReal := by
  have hK : IsOpen (K : Set G) := Subgroup.isOpen_mono hle hH
  exact toReal_eq_relIndex_mul μ H K hle hK.measurableSet hH.measurableSet
    (hH.measure_ne_zero μ ⟨1, H.one_mem⟩)
end MassDataLevelSSteps
