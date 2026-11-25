-- Prove2me | solution 1 for GlobalTheory.Cube.cubeSign_inlEmb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T08:19:52.832062+00:00
-- url     : https://prove2.me/submissions/cba1782e-4432-4273-a6f9-e842fb623e95

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_CubeTotalComplexAcyclicOfSlicesInductionOnCard
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_RangeRestrictCompSubtypeOfOrthogonalOfNe
import Theorems.Thm_GlobalTheory_Cube_card_parts

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
theorem _root_.solution (w : Finset (ι ⊕ₗ κ)) (i : ι) :
    cubeSign w (inlEmb ι κ i) = cubeSign (part (inlEmb ι κ) w) i := by
  have h1 : part (inlEmb ι κ) (w.filter (· < inlEmb ι κ i)) =
      (part (inlEmb ι κ) w).filter (· < i) := by
    ext; rw [mem_part, Finset.mem_filter]; simp
  have h2 : part (inrEmb ι κ) (w.filter (· < inlEmb ι κ i)) = ∅ := by
    ext; rw [mem_part, Finset.mem_filter]; simp
  rw [cubeSign, card_parts, h1, h2, cubeSign]
  simp
end GlobalTheory.Cube
