-- Prove2me | solution 1 for GlobalTheory.Cube.cubeSign_inrEmb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T08:19:55.344084+00:00
-- url     : https://prove2.me/submissions/c41c55d0-b994-4085-85fe-09465f728909

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
theorem _root_.solution (w : Finset (ι ⊕ₗ κ)) (k : κ) :
    cubeSign w (inrEmb ι κ k) =
      (-1) ^ (part (inlEmb ι κ) w).card * cubeSign (part (inrEmb ι κ) w) k := by
  have h1 : part (inlEmb ι κ) (w.filter (· < inrEmb ι κ k)) = part (inlEmb ι κ) w := by
    ext; rw [mem_part, Finset.mem_filter]; simp
  have h2 : part (inrEmb ι κ) (w.filter (· < inrEmb ι κ k)) =
      (part (inrEmb ι κ) w).filter (· < k) := by
    ext; rw [mem_part, Finset.mem_filter]; simp
  rw [cubeSign, card_parts, h1, h2, cubeSign, pow_add]
end GlobalTheory.Cube
