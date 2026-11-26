-- Prove2me | solution 1 for HajnalSzemeredi.proper_update
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T22:45:26.695335+00:00
-- url     : https://prove2.me/submissions/8cb938ee-b5d7-406f-939b-c37f684dd3ae

module
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Logic.Relation
public import Mathlib.Order.Interval.Finset.Nat
public import Definitions.Def_HajnalSzemeredi_Defs
public import Theorems.Thm_HajnalSzemeredi_mem_cls
public import Theorems.Thm_HajnalSzemeredi_mem_nbr
attribute [local simp] HajnalSzemeredi.mem_cls
attribute [local simp] HajnalSzemeredi.mem_nbr

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open Classical Finset
open HajnalSzemeredi
variable {V : Type*} (G : SimpleGraph V)
variable {G}
variable {S : Finset V} {c : V → ℕ} {v : V} {j : ℕ}
namespace HajnalSzemeredi
theorem _root_.solution (h : Proper G S c) (hmov : Movable G S c v j) :
    Proper G S (Function.update c v j) := by
  intro a ha b hb hab
  by_cases hav : a = v
  · subst hav
    have hbv : b ≠ a := fun h => G.loopless.irrefl _ (h ▸ hab)
    simp only [Function.update_self, Function.update_of_ne hbv]
    intro hjb
    exact hmov b (mem_cls.mpr ⟨hb, hjb.symm⟩) hab
  · by_cases hbv : b = v
    · subst hbv
      simp only [Function.update_self, Function.update_of_ne hav]
      intro hja
      exact hmov a (mem_cls.mpr ⟨ha, hja⟩) hab.symm
    · simpa [Function.update_of_ne hav, Function.update_of_ne hbv] using h a ha b hb hab
end HajnalSzemeredi
