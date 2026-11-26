-- Prove2me | solution 1 for HajnalSzemeredi.into_update
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T22:46:07.623882+00:00
-- url     : https://prove2.me/submissions/4331b031-4278-431d-a52d-5e9463e243f2

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
theorem _root_.solution {P : Finset ℕ} (h : Into S c P) (hj : j ∈ P) :
    Into S (Function.update c v j) P := by
  intro w hw
  by_cases hwv : w = v
  · subst hwv; simpa using hj
  · simpa [hwv] using h w hw
end HajnalSzemeredi
