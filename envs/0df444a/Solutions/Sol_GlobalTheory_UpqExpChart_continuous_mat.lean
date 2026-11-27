-- Prove2me | solution 1 for GlobalTheory.UpqExpChart.continuous_mat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T04:36:42.226601+00:00
-- url     : https://prove2.me/submissions/01762415-4587-4ec3-909b-4ce4d07667eb

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_DataCD
import Definitions.Def_Formalism_SatakeDualWeyl_KpqSubgroupCompact
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ContinuousMatExp
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
theorem _root_.solution {P Q : ℕ} : Continuous (UpqT.mat : UpqT P Q → _) :=
  Units.continuous_val.comp continuous_subtype_val
end GlobalTheory.UpqExpChart
