-- Prove2me | solution 1 for GlobalTheory.KuennethOne.MM_surj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T18:33:51.497199+00:00
-- url     : https://prove2.me/submissions/bce247ab-391b-4436-80ae-129333075c4c

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
    (hU : ∀ i, IsAffineOpen (U i)) (hW : IsAffineOpen W)
    (c : ∀ i, Γ(Z, p ⁻¹ᵁ U i ⊓ q ⁻¹ᵁ W)) :
    ∃ z, ∀ i, MM H U W i _ inf_le_left inf_le_right z = c i := by
  classical
  have := Fintype.ofFinite ι
  choose w hw using fun i => (mm_bijective H (hU i) hW).2 (c i)
  refine ⟨(TensorProduct.piLeft _ _ _).symm w, fun i => ?_⟩
  rw [MM_eq, LinearEquiv.apply_symm_apply, hw]
end GlobalTheory.KuennethOne
