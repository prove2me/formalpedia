-- Prove2me | solution 1 for GlobalTheory.Cube.card_parts
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:07:48.58079+00:00
-- url     : https://prove2.me/submissions/ac84fa86-e89b-4dce-bc93-2cd26ebff57d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_CubeTotalComplexAcyclicOfSlicesInductionOnCard
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_RangeRestrictCompSubtypeOfOrthogonalOfNe
import Theorems.Thm_GlobalTheory_Cube_sum_parts

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits HomologicalComplex TensorProduct
universe v u
open GlobalTheory
open GlobalTheory.Cube
variable {ι κ : Type} [LinearOrder ι] [LinearOrder κ] {K : Type u} [CommRing K]
namespace GlobalTheory.Cube
theorem _root_.solution (w : Finset (ι ⊕ₗ κ)) :
    w.card = (part (inlEmb ι κ) w).card + (part (inrEmb ι κ) w).card := by
  simp only [Finset.card_eq_sum_ones]
  exact sum_parts w _
end GlobalTheory.Cube
