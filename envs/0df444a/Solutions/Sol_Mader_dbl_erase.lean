-- Prove2me | solution 1 for Mader.dbl_erase
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T04:51:47.179924+00:00
-- url     : https://prove2.me/submissions/cc5b9c97-919e-4f7c-b3a2-0b2301a4cf8e

module
public import Mathlib
public import Definitions.Def_MaderLib_MaderAux

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph Finset
open Mader
variable {V : Type*}
variable (G : SimpleGraph V)
open Classical
namespace Mader
theorem _root_.solution {S : Finset V} {v : V} (hv : v ∈ S) :
    dbl G S ≤ dbl G (S.erase v) + 2 * ndeg G S v := by
  classical
  have hsub : (S ×ˢ S).filter (fun p => G.Adj p.1 p.2) ⊆
      ((S.erase v ×ˢ S.erase v).filter (fun p => G.Adj p.1 p.2) ∪
        (S.filter (G.Adj v)).image (fun w => (v, w))) ∪
        (S.filter (G.Adj v)).image (fun w => (w, v)) := by
    rintro ⟨a, b⟩ h
    simp only [mem_filter, mem_product] at h
    simp only [mem_union, mem_filter, mem_product, mem_erase, mem_image, Prod.mk.injEq]
    by_cases ha : a = v
    · subst ha; left; right; exact ⟨b, ⟨h.1.2, h.2⟩, rfl, rfl⟩
    by_cases hb : b = v
    · subst hb; right; exact ⟨a, ⟨h.1.1, h.2.symm⟩, rfl, rfl⟩
    left; left; exact ⟨⟨⟨ha, h.1.1⟩, hb, h.1.2⟩, h.2⟩
  unfold dbl ndeg
  have h0 := card_le_card hsub
  have h1 := card_union_le (((S.erase v ×ˢ S.erase v).filter (fun p => G.Adj p.1 p.2) ∪
        (S.filter (G.Adj v)).image (fun w => (v, w))))
        ((S.filter (G.Adj v)).image (fun w => (w, v)))
  have h2 := card_union_le ((S.erase v ×ˢ S.erase v).filter (fun p => G.Adj p.1 p.2))
        ((S.filter (G.Adj v)).image (fun w => (v, w)))
  have h3 := card_image_le (s := S.filter (G.Adj v)) (f := fun w => (v, w))
  have h4 := card_image_le (s := S.filter (G.Adj v)) (f := fun w => (w, v))
  omega
end Mader
