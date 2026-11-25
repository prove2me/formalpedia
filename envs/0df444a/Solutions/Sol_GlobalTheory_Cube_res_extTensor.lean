-- Prove2me | solution 1 for GlobalTheory.Cube.res_extTensor
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:37:32.704511+00:00
-- url     : https://prove2.me/submissions/f17d4b78-8897-4f0a-bc11-e3a4aba94089

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
namespace GlobalTheory.Cube
theorem _root_.solution (A : Cube.{v} ι K) (B : Cube.{v} κ K) {w w' : Finset (ι ⊕ₗ κ)}
    (h : w ⊆ w') : res (extTensor A B) h =
      TensorProduct.map (res A (monotone_part _ h)) (res B (monotone_part _ h)) := rfl
end GlobalTheory.Cube
