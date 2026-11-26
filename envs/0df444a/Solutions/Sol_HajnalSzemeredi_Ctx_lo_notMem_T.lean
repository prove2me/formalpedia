-- Prove2me | solution 1 for HajnalSzemeredi.Ctx.lo_notMem_T
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T22:45:57.210848+00:00
-- url     : https://prove2.me/submissions/4523a000-8e8a-46e6-8b12-b79203f4dc64

module
public import Definitions.Def_HajnalSzemeredi_Count
public import Definitions.Def_HajnalSzemeredi_Reach
public import Mathlib.Combinatorics.Enumerative.DoubleCounting
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Tactic.Ring
public import Definitions.Def_HajnalSzemeredi_Structure

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open Classical Finset Relation
open HajnalSzemeredi
variable {V : Type*} {G : SimpleGraph V}
open HajnalSzemeredi.Ctx
variable {S : Finset V} {P : Finset ℕ} {c : V → ℕ} {r s lo hi : ℕ}
namespace HajnalSzemeredi.Ctx
theorem _root_.solution (W : ℕ) : lo ∉ T G S P c lo W := by
  intro hmem
  exact (mem_filter.mp hmem).2 ReflTransGen.refl
end HajnalSzemeredi.Ctx
