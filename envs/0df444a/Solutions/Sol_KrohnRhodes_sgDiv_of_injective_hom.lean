-- Prove2me | solution 1 for KrohnRhodes.sgDiv_of_injective_hom
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T03:56:10.956124+00:00
-- url     : https://prove2.me/submissions/56fee2d9-9c4d-4e3c-80a0-055c3db2a756

module
public import Definitions.Def_KrohnRhodes_Defs
public import Definitions.Def_KrohnRhodes_Foundations_WreathProduct
public import Mathlib
public import Definitions.Def_KrohnRhodes_Foundations_MonoidWreathBridge
public import Definitions.Def_KrohnRhodes_Foundations_KrasnerKaloujnine
public import Definitions.Def_KrohnRhodes_Foundations_Division

set_option autoImplicit true
@[expose] public section
public section
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.style.show false
open KrohnRhodes
universe u
namespace KrohnRhodes
theorem _root_.solution {S T W : Type u} [Mul S] [Mul T] [Mul W]
    (h : SgDiv S T) (ι : T →ₙ* W) (hι : Function.Injective ι) :
    SgDiv S W := by
  obtain ⟨U, φ, hφ⟩ := h
  -- `ι.subsemigroupMap U : U →ₙ* U.map ι` is bijective.
  have hbij : Function.Bijective (ι.subsemigroupMap U) := by
    refine ⟨?_, MulHom.subsemigroupMap_surjective ι U⟩
    intro a b hab
    apply Subtype.ext
    apply hι
    exact congrArg Subtype.val hab
  -- Hence `U ≃* U.map ι`.
  let e : U ≃* U.map ι := MulEquiv.ofBijective (ι.subsemigroupMap U) hbij
  -- Compose `φ` with the inverse iso to get a surjective hom `U.map ι →ₙ* S`.
  refine ⟨U.map ι, φ.comp e.symm.toMulHom, ?_⟩
  intro s
  obtain ⟨u, hu⟩ := hφ s
  refine ⟨e u, ?_⟩
  change φ (e.symm (e u)) = s
  rw [e.symm_apply_apply, hu]
end KrohnRhodes
