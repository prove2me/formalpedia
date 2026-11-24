-- Prove2me | solution 1 for GlobalTheory.KuennethOne.dlt_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T18:33:46.488128+00:00
-- url     : https://prove2.me/submissions/858c706b-77aa-455f-92d3-ea9aaab854e3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsSplitsOfIsAffineOpen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_MemRangeRTensorOfForallDual

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace TensorProduct
open GlobalTheory GlobalTheory.KuennethOne
variable {S X Y Z T : Scheme.{0}}
variable {p : Z ⟶ X} {q : Z ⟶ Y} {iX : X ⟶ S} {iY : Y ⟶ S} (H : IsPullback p q iX iY)
variable {ι : Type}
namespace GlobalTheory.KuennethOne
theorem _root_.solution (iX : X ⟶ S) (U : ι → X.Opens) (x : ∀ i, Fn iX (U i)) (k : ι × ι) :
    dlt iX U x k = (rs inf_le_left (x k.1) - rs inf_le_right (x k.2) : Γ(X, U k.1 ⊓ U k.2)) := rfl
end GlobalTheory.KuennethOne
