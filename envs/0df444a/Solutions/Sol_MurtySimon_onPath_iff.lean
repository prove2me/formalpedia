-- Prove2me | solution 1 for MurtySimon.onPath_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T22:54:17.174867+00:00
-- url     : https://prove2.me/submissions/904ed321-4d0d-4df4-a60b-7038eb08d10c

module
public import Definitions.Def_MurtySimon_Defs
public import Definitions.Def_MurtySimon_Basic
public import Theorems.Thm_MurtySimon_IsMid_symm
public import Theorems.Thm_MurtySimon_IsMid_unique_of_eq

set_option autoImplicit true
@[expose] public section
public section
open MurtySimon
open Finset SimpleGraph
variable {V : Type*} (G : SimpleGraph V)
variable {G}
namespace MurtySimon
theorem _root_.solution {x y u : V} (h : IsMid G x y u) {e : Sym2 V} :
    OnPath G e s(x, y) ↔ e = s(x, u) ∨ e = s(u, y) := by
  constructor
  · rintro ⟨x', y', u', hf, hm, rfl⟩
    have hu : u' = u := h.unique_of_eq hf hm
    subst hu
    rcases Sym2.eq_iff.1 hf with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Or.inl rfl
    · exact Or.inr Sym2.eq_swap
  · rintro (rfl | rfl)
    · exact ⟨x, y, u, rfl, h, rfl⟩
    · exact ⟨y, x, u, Sym2.eq_swap, h.symm, Sym2.eq_swap⟩
end MurtySimon
