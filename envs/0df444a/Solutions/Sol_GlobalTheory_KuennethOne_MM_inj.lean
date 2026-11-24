-- Prove2me | solution 1 for GlobalTheory.KuennethOne.MM_inj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T18:33:49.663077+00:00
-- url     : https://prove2.me/submissions/c96641a8-cc2a-4755-9b23-88724354a518

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsSplitsOfIsAffineOpen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_MemRangeRTensorOfForallDual
import Theorems.Thm_GlobalTheory_KuennethOne_mm_bijective
import Theorems.Thm_GlobalTheory_KuennethOne_MM_eq

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
theorem _root_.solution [IsAffine S] [Finite ι] {U : ι → X.Opens} {W : Y.Opens}
    (hU : ∀ i, IsAffineOpen (U i)) (hW : IsAffineOpen W) (z)
    (h : ∀ i, MM H U W i _ inf_le_left inf_le_right z = 0) : z = 0 := by
  classical
  have := Fintype.ofFinite ι
  apply (TensorProduct.piLeft _ _ _).injective
  funext i
  apply (mm_bijective H (hU i) hW).1
  rw [← MM_eq, h, map_zero, Pi.zero_apply, map_zero]
  rfl
end GlobalTheory.KuennethOne
