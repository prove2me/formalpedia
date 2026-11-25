-- Prove2me | solution 1 for GlobalTheory.CompactDualQuot.continuous_ptGauge
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:33:49.470453+00:00
-- url     : https://prove2.me/submissions/b054524d-3074-4107-8583-d0213d61742a

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_DataCD
import Definitions.Def_Formalism_SharpRestriction_GlobalSchurBounds_GeneralLinearActions_GenusMassVolumes
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_GlobalSignature_PerpendicularEmbedding
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ContinuousMatrixEntryAbsSum

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
theorem _root_.solution (e : Option (Fin P' ⊕ Fin Q') ≃ (Fin P ⊕ Fin Q)) :
    Continuous (ptGauge e) := by
  unfold ptGauge; fun_prop
end GlobalTheory.CompactDualQuot
