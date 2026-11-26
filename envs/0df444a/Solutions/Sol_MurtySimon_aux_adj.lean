-- Prove2me | solution 1 for MurtySimon.aux_adj
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T22:54:23.302902+00:00
-- url     : https://prove2.me/submissions/deec6fef-8057-4aa4-9afa-822a993522b1

module
public import Definitions.Def_MurtySimon_Defs
public import Definitions.Def_MurtySimon_Basic
public import Theorems.Thm_MurtySimon_OnPath_ne

set_option autoImplicit true
@[expose] public section
public section
open MurtySimon
open Finset SimpleGraph
variable {V : Type*} (G : SimpleGraph V)
variable {G}
namespace MurtySimon
theorem _root_.solution {M : Finset (Sym2 V)} {e f : Sym2 V} :
    (aux G M).Adj e f ↔ (e ∉ M ∧ OnPath G e f) ∨ (f ∉ M ∧ OnPath G f e) := by
  rw [aux, fromRel_adj]
  constructor
  · exact fun h => h.2
  · intro h
    refine ⟨?_, h⟩
    rintro rfl
    rcases h with h | h <;> exact h.2.ne rfl
end MurtySimon
