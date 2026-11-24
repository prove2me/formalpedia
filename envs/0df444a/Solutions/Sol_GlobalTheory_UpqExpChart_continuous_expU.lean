-- Prove2me | solution 1 for GlobalTheory.UpqExpChart.continuous_expU
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T20:35:49.371649+00:00
-- url     : https://prove2.me/submissions/d148b8ef-6887-4b3b-a7eb-3ae1945b4825

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_DataCD
import Definitions.Def_Formalism_SatakeDualWeyl_KpqSubgroupCompact
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ContinuousMatExp
import Theorems.Thm_GlobalTheory_UpqExpChart_continuous_matExp
import Theorems.Thm_Formalism_UG_Final_KpqSubgroupCompact


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.BasicNotions MeasureTheory Filter Topology Matrix
noncomputable section
open GlobalTheory GlobalTheory.UpqExpChart
namespace GlobalTheory.UpqExpChart
theorem _root_.solution (P Q : ℕ) : Continuous (expU P Q) := by
  refine Continuous.subtype_mk (Units.continuous_iff.2 ⟨?_, ?_⟩) _
  · exact continuous_matExp.comp continuous_subtype_val
  · exact continuous_matExp.comp continuous_subtype_val.neg
end GlobalTheory.UpqExpChart
