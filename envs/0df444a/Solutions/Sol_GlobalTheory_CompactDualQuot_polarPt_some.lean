-- Prove2me | solution 1 for GlobalTheory.CompactDualQuot.polarPt_some
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:30:38.831846+00:00
-- url     : https://prove2.me/submissions/7b488049-7544-4e8f-947e-e26c8ad0bf6d

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
theorem _root_.solution (e : Option (Fin P' ⊕ Fin Q') ≃ (Fin P ⊕ Fin Q)) (t : ℝ × Sp P' Q')
    (i : Fin P' ⊕ Fin Q') : polarPt e t (e (some i)) = t.2 i := by
  simp [polarPt]
end GlobalTheory.CompactDualQuot
