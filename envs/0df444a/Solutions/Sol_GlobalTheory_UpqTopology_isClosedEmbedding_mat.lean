-- Prove2me | solution 1 for GlobalTheory.UpqTopology.isClosedEmbedding_mat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:44:51.465209+00:00
-- url     : https://prove2.me/submissions/ae6d71c7-14bc-4494-85fc-2a340338da77

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_DataCD
import Definitions.Def_Formalism_SatakeDualWeyl_KpqSubgroupCompact
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_UpqLocallyCompactGroup
import Theorems.Thm_GlobalTheory_UpqTopology_range_mat
import Theorems.Thm_GlobalTheory_UpqTopology_isInducing_mat
import Theorems.Thm_Formalism_UG_Final_KpqSubgroupCompact


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism.BasicNotions MeasureTheory Filter Topology Matrix
open GlobalTheory GlobalTheory.UpqTopology
variable {P Q : ℕ}
namespace GlobalTheory.UpqTopology
theorem _root_.solution : IsClosedEmbedding (UpqT.mat (P := P) (Q := Q)) := by
  refine ⟨⟨isInducing_mat, fun _ _ h => Subtype.ext (Units.ext h)⟩, ?_⟩
  rw [range_mat]
  exact isClosed_eq ((continuous_id.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul
    continuous_id) continuous_const
end GlobalTheory.UpqTopology
