-- Prove2me | solution 1 for GlobalTheory.CompactDualQuot.qf_baseVec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:30:51.731539+00:00
-- url     : https://prove2.me/submissions/072b5b9b-34e3-4330-bb60-cb79230dbe61

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_DataCD
import Definitions.Def_Formalism_SharpRestriction_GlobalSchurBounds_GeneralLinearActions_GenusMassVolumes
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_GlobalSignature_PerpendicularEmbedding
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ContinuousMatrixEntryAbsSum
import Theorems.Thm_GlobalTheory_CompactDualQuot_qf_eq_sum

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
    qf (baseVec e) = sg (e none) := by
  rw [qf_eq_sum, Finset.sum_eq_single (e none)]
  · simp [baseVec]
  · intro b _ hb; simp [baseVec, hb]
  · simp
end GlobalTheory.CompactDualQuot
