-- Prove2me | solution 1 for GlobalTheory.KuennethOne.mm_bijective
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:40:37.602806+00:00
-- url     : https://prove2.me/submissions/b86c8e50-3955-4984-a986-4495f908eb2a

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
namespace GlobalTheory.KuennethOne
theorem _root_.solution [IsAffine S] {U : X.Opens} {W : Y.Opens} (hU : IsAffineOpen U)
    (hW : IsAffineOpen W) :
    Function.Bijective (mm H U W (p ⁻¹ᵁ U ⊓ q ⁻¹ᵁ W) inf_le_left inf_le_right) := by
  have po := (isIso_pushoutSection_iff H (US := ⊤) (UT := W) (UX := U) le_top le_top rfl).1
    (isIso_pushoutSection_of_isAffineOpen H _ _ _ (isAffineOpen_top _) hW hU)
  have h1 := CommRingCat.isPushout_tensorProduct Γ(S, ⊤) (Fn iX U) (Fn iY W)
  let e := h1.isoIsPushout _ _ po
  have : e.hom = CommRingCat.ofHom
      (mm H U W (p ⁻¹ᵁ U ⊓ q ⁻¹ᵁ W) inf_le_left inf_le_right).toRingHom := by
    refine h1.hom_ext ?_ ?_
    · refine (h1.inl_isoIsPushout_hom _ _ po).trans ?_
      ext x
      exact (Algebra.TensorProduct.productMap_left_apply (pb p rfl U _ inf_le_left)
        (pb q H.w.symm W _ inf_le_right) x).symm
    · refine (h1.inr_isoIsPushout_hom _ _ po).trans ?_
      ext x
      exact (Algebra.TensorProduct.productMap_right_apply (pb p rfl U _ inf_le_left)
        (pb q H.w.symm W _ inf_le_right) x).symm
  have hb := ConcreteCategory.bijective_of_isIso e.hom
  rw [this] at hb
  exact hb
end GlobalTheory.KuennethOne
