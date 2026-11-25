-- Prove2me | solution 1 for GlobalTheory.CompactDualQuot.polarPt_none
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:30:34.901644+00:00
-- url     : https://prove2.me/submissions/09496e7f-7894-4bcb-8422-2be26843f4c4

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
theorem _root_.solution (e : Option (Fin P' ⊕ Fin Q') ≃ (Fin P ⊕ Fin Q)) (t : ℝ × Sp P' Q') :
    polarPt e t (e none) =
      (Real.sqrt (1 - sg (e none) * qf t.2) : ℂ) * Complex.exp ((t.1 : ℂ) * Complex.I) := by
  simp [polarPt]
end GlobalTheory.CompactDualQuot
