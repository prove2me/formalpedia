-- Prove2me | solution 1 for MurtySimon.card_neighborFinset_right_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T22:56:18.813357+00:00
-- url     : https://prove2.me/submissions/e165f174-1d5d-4747-801c-239ff47f4da2

module
public import Definitions.Def_MurtySimon_Basic
public import Definitions.Def_MurtySimon_Components
public import Theorems.Thm_MurtySimon_mem_Rt
public import Theorems.Thm_MurtySimon_mem_neighborFinset_right

set_option autoImplicit true
@[expose] public section
public section
open MurtySimon
open Finset SimpleGraph
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
noncomputable section
namespace MurtySimon
theorem _root_.solution {M : Finset (Sym2 V)} {f : Sym2 V} (hf : f ∈ Rt G) :
    #((aux G M).neighborFinset f) ≤ 2 := by
  obtain ⟨x, y, u, rfl, h⟩ := mem_Rt.1 hf
  calc #((aux G M).neighborFinset s(x, y)) ≤ #({s(x, u), s(u, y)} : Finset (Sym2 V)) := by
        apply card_le_card
        intro e he
        rcases ((mem_neighborFinset_right h).1 he).1 with rfl | rfl <;> simp
    _ ≤ 2 := card_le_two
end MurtySimon
