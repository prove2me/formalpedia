-- Prove2me | solution 1 for MassDataLevelSSteps.toReal_eq_relIndex_mul_of_haar
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:49:56.203052+00:00
-- url     : https://prove2.me/submissions/cbf6f888-d57c-4458-b1db-2b8f19c03763

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelStructures_HaarIdx
import Theorems.Thm_MassDataLevelSSteps_toReal_eq_relIndex_mul_of_open

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
theorem _root_.solution {G : Type} [Group G] [TopologicalSpace G] [MeasurableSpace G]
    (hc : ContinuousMul G) (hB : BorelSpace G) (μ : Measure G) (hμ : μ.IsHaarMeasure)
    (H K : Subgroup G) (hle : H ≤ K) (hH : IsOpen (H : Set G)) :
    (μ K).toReal = (H.relIndex K : ℝ) * (μ H).toReal := by
  haveI := hc
  haveI := hB
  haveI := hμ
  exact toReal_eq_relIndex_mul_of_open μ H K hle hH
end MassDataLevelSSteps
