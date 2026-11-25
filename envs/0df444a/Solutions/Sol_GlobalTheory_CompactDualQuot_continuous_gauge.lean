-- Prove2me | solution 1 for GlobalTheory.CompactDualQuot.continuous_gauge
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:33:45.304215+00:00
-- url     : https://prove2.me/submissions/11a0e43b-3b56-48f2-a2ce-f338641b4190

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_DataCD
import Definitions.Def_Formalism_SharpRestriction_GlobalSchurBounds_GeneralLinearActions_GenusMassVolumes
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_GlobalSignature_PerpendicularEmbedding
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ContinuousMatrixEntryAbsSum
import Theorems.Thm_GlobalTheory_CompactDualQuot_continuous_matrixEntryAbsSum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompactDualQuot
open MeasureTheory Matrix Filter Topology Formalism.BasicNotions GlobalTheory.IndefiniteRowSideFullHecke.PerpendicularEmbedding
open scoped ENNReal
variable {P Q P' Q' : ℕ}
namespace GlobalTheory.CompactDualQuot
theorem _root_.solution : Continuous (gauge : UpqT P Q → ℝ) :=
  continuous_matrixEntryAbsSum.comp
    ((Units.continuous_val.comp continuous_subtype_val : Continuous UpqT.mat).sub continuous_const)
end GlobalTheory.CompactDualQuot
