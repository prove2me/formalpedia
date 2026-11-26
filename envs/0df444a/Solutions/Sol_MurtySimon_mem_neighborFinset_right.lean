-- Prove2me | solution 1 for MurtySimon.mem_neighborFinset_right
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T22:55:33.04997+00:00
-- url     : https://prove2.me/submissions/8b62e9ea-8ce9-42b9-bf4a-3fec541fca31

module
public import Definitions.Def_MurtySimon_Basic
public import Definitions.Def_MurtySimon_Components
public import Theorems.Thm_MurtySimon_OnPath_mem_edgeSet
public import Theorems.Thm_MurtySimon_aux_adj
public import Theorems.Thm_MurtySimon_onPath_iff


set_option autoImplicit true
@[expose] public section
public section
open MurtySimon
open Finset SimpleGraph
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
noncomputable section
namespace MurtySimon
theorem _root_.solution {M : Finset (Sym2 V)} {x y u : V} (h : IsMid G x y u)
    {e : Sym2 V} : e ∈ (aux G M).neighborFinset s(x, y) ↔ (e = s(x, u) ∨ e = s(u, y)) ∧ e ∉ M := by
  rw [mem_neighborFinset, aux_adj]
  constructor
  · rintro (⟨-, h'⟩ | ⟨h1, h2⟩)
    · exact absurd h'.mem_edgeSet h.2.1
    · exact ⟨(onPath_iff h).1 h2, h1⟩
  · rintro ⟨h1, h2⟩
    exact Or.inr ⟨h2, (onPath_iff h).2 h1⟩
end MurtySimon
