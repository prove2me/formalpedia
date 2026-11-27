-- Prove2me | solution 1 for GlobalTheory.preimage_eq_of_finite_appLE
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T04:41:56.635268+00:00
-- url     : https://prove2.me/submissions/66bc1ff7-e83a-4a3f-ada4-613499c67fd9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PreimageEqOfFiniteAppLE

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution : ∀ {X Y : Scheme.{0}} [IsIntegral Y] (π : Y ⟶ X) [IsSeparated π] {U : X.Opens} {V : Y.Opens}, IsAffineOpen U → IsAffineOpen V → (V : Set Y).Nonempty → ∀ h : V ≤ π ⁻¹ᵁ U, (π.appLE U V h).hom.Finite → π ⁻¹ᵁ U = V := by
  intro X Y _ π _ U V hU hV hne h hfin
  have : IsAffine U := hU
  have : IsAffine V := hV
  have hf : IsFinite (π.resLE U V h) := by
    have hS : IsFinite (Spec.map (π.resLE U V h).appTop) := (IsFinite.SpecMap_iff _).mpr
      ((RingHom.finite_respectsIso.arrow_mk_iso_iff (arrowResLEAppIso π U V h)).mpr hfin)
    rw [Arrow.iso_w' (arrowIsoSpecΓOfIsAffine (π.resLE U V h)).symm]
    infer_instance
  have : UniversallyClosed (Y.homOfLE h ≫ π ∣_ U) := by
    change UniversallyClosed (π.resLE U V h)
    infer_instance
  have : UniversallyClosed (Y.homOfLE h) := .of_comp_of_isSeparated _ (π ∣_ U)
  obtain ⟨y, hy⟩ := hne
  have : Nonempty (π ⁻¹ᵁ U) := ⟨⟨y, h hy⟩⟩
  have hcl : IsClopen (Set.range (Y.homOfLE h).base) :=
    ⟨(Y.homOfLE h).isClosedMap.isClosed_range,
      (Y.homOfLE h).isOpenEmbedding.isOpenMap.isOpen_range⟩
  have huniv : Set.range (Y.homOfLE h).base = Set.univ :=
    (isClopen_iff.mp hcl).resolve_left
      (Set.nonempty_iff_ne_empty.mp ⟨_, ⟨⟨y, hy⟩, rfl⟩⟩)
  refine le_antisymm (fun x hx => ?_) h
  obtain ⟨⟨w, hw⟩, hz⟩ : (⟨x, hx⟩ : π ⁻¹ᵁ U) ∈ Set.range (Y.homOfLE h).base := by
    rw [huniv]; trivial
  have hz' : ((Y.homOfLE h) ⟨w, hw⟩).1 = x := congrArg Subtype.val hz
  have hzx : w = x := (Scheme.homOfLE_apply h ⟨w, hw⟩).symm.trans hz'
  exact hzx ▸ hw
end GlobalTheory
