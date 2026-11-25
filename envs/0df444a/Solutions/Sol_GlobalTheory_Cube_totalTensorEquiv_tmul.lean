-- Prove2me | solution 1 for GlobalTheory.Cube.totalTensorEquiv_tmul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T07:44:17.912096+00:00
-- url     : https://prove2.me/submissions/20e2c5cb-23c2-4a24-b862-57fe6d03e32c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_CubeTotalComplexAcyclicOfSlicesInductionOnCard
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_RangeRestrictCompSubtypeOfOrthogonalOfNe

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
variable [Finite ι] [Finite κ] (A : Cube.{v} ι K) (B : Cube.{v} κ K)
namespace GlobalTheory.Cube
theorem _root_.solution (x : ∀ s, A.obj s) (y : ∀ t, B.obj t) (w : Finset (ι ⊕ₗ κ)) :
    totalTensorEquiv A B (x ⊗ₜ y) w = x (part (inlEmb ι κ) w) ⊗ₜ[K] y (part (inrEmb ι κ) w) := rfl
end GlobalTheory.Cube
