-- Prove2me | solution 1 for HajnalSzemeredi.mem_cls
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T22:44:19.160577+00:00
-- url     : https://prove2.me/submissions/cf483e9b-d216-4ab7-90ec-bc31dfcd68e0

module
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Logic.Relation
public import Mathlib.Order.Interval.Finset.Nat
public import Definitions.Def_HajnalSzemeredi_Defs

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open Classical Finset
open HajnalSzemeredi
variable {V : Type*} (G : SimpleGraph V)
variable {G}
namespace HajnalSzemeredi
theorem _root_.solution {S : Finset V} {c : V → ℕ} {i : ℕ} {v : V} :
    v ∈ cls S c i ↔ v ∈ S ∧ c v = i := by
  simp [cls]
end HajnalSzemeredi
