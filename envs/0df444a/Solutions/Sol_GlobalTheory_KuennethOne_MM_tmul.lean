-- Prove2me | solution 1 for GlobalTheory.KuennethOne.MM_tmul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:48:20.74312+00:00
-- url     : https://prove2.me/submissions/90c943c1-bd1f-4c1e-b9cb-f88ea10db196

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
theorem _root_.solution (U : ι → X.Opens) (W : Y.Opens) (i : ι) (O : Z.Opens) (hU : O ≤ p ⁻¹ᵁ U i)
    (hW : O ≤ q ⁻¹ᵁ W) (a : ∀ i, Fn iX (U i)) (b : Fn iY W) :
    MM H U W i O hU hW (a ⊗ₜ b) = (p.appLE (U i) O hU).hom (a i) * (q.appLE W O hW).hom b := rfl
end GlobalTheory.KuennethOne
