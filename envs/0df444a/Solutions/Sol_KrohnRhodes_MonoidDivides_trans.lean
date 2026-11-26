-- Prove2me | solution 1 for KrohnRhodes.MonoidDivides.trans
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T03:53:48.190392+00:00
-- url     : https://prove2.me/submissions/4e612430-439a-4b13-93b0-af3ab54baa07

module
public import Definitions.Def_KrohnRhodes_Defs
public import Mathlib
public import Definitions.Def_KrohnRhodes_Foundations_WreathProduct
public import Definitions.Def_KrohnRhodes_Foundations_LocalDivisor

set_option autoImplicit true
@[expose] public section
public section
open FreeMonoid Computability Pointwise
universe u
variable {α : Type u}
open KrohnRhodes
namespace KrohnRhodes
namespace MonoidDivides
theorem _root_.solution {M N P : Type*} [Monoid M] [Monoid N] [Monoid P]
    (h1 : MonoidDivides M N) (h2 : MonoidDivides N P) : MonoidDivides M P := by
  obtain ⟨S, φ, hφ⟩ := h1
  obtain ⟨T, ψ, hψ⟩ := h2
  -- `U := ψ⁻¹(S) ≤ T`; `ψ'` corestricts `ψ|U` to `S`.
  let U : Submonoid T := S.comap ψ
  let ψ' : U →* S := (ψ.comp U.subtype).codRestrict S (fun x => x.2)
  have hψ'_surj : Function.Surjective ψ' := by
    intro s
    obtain ⟨t, ht⟩ := hψ s
    exact ⟨⟨t, by show ψ t ∈ S; rw [ht]; exact s.2⟩, by apply Subtype.ext; show ψ t = s; rw [ht]⟩
  -- Transport `U` to a submonoid `V ≤ P` via the injective inclusion `T ↪ P`.
  let V : Submonoid P := U.map T.subtype
  let eUV : U ≃* V := Submonoid.equivMapOfInjective U T.subtype Subtype.val_injective
  exact ⟨V, (φ.comp ψ').comp eUV.symm.toMonoidHom,
    (hφ.comp hψ'_surj).comp eUV.symm.surjective⟩
end MonoidDivides
end KrohnRhodes
