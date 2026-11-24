-- Prove2me | solution 1 for GlobalTheory.CompactDualQuot.continuous_matrixEntryAbsSum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T12:15:55.149809+00:00
-- url     : https://prove2.me/submissions/2b2ddfd7-2301-4977-8406-a5a64f2a9a34

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
theorem _root_.solution : Continuous (l1 : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ → ℝ) :=
  continuous_finset_sum _ fun i _ => continuous_finset_sum _ fun j _ =>
    (continuous_id.matrix_elem i j).norm
end GlobalTheory.CompactDualQuot
