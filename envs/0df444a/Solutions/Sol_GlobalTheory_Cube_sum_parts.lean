-- Prove2me | solution 1 for GlobalTheory.Cube.sum_parts
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T07:44:15.033797+00:00
-- url     : https://prove2.me/submissions/b75b17bc-6aa1-4f80-a8a8-985a0db87dc7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_CubeTotalComplexAcyclicOfSlicesInductionOnCard
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_RangeRestrictCompSubtypeOfOrthogonalOfNe
import Theorems.Thm_GlobalTheory_Cube_sumVertex_eq_map_disjSum


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
theorem _root_.solution {M : Type*} [AddCommMonoid M] (w : Finset (ι ⊕ₗ κ)) (F : ι ⊕ₗ κ → M) :
    ∑ j ∈ w, F j = ∑ i ∈ part (inlEmb ι κ) w, F (inlEmb ι κ i) +
      ∑ k ∈ part (inrEmb ι κ) w, F (inrEmb ι κ k) := by
  conv_lhs => rw [← sumVertex_part w, sumVertex_eq_map_disjSum, Finset.sum_map, Finset.sum_disjSum]
  rfl
end GlobalTheory.Cube
