-- Prove2me | solution 1 for GlobalTheory.CompactDualQuot.weightAbsEntrySum_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:31:13.789924+00:00
-- url     : https://prove2.me/submissions/9562fab2-c35f-448d-a8a4-0f1bfdca8b46

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
theorem _root_.solution (Z : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ) : 0 ≤ l1 Z :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _
end GlobalTheory.CompactDualQuot
