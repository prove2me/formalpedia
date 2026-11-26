-- Prove2me | solution 1 for HajnalSzemeredi.Ctx.acc_subset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T22:45:12.969883+00:00
-- url     : https://prove2.me/submissions/dbcc4d34-328d-4fe5-ab93-928daf1375b5

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
theorem _root_.solution : acc G S P c lo ⊆ P := filter_subset _ _
end HajnalSzemeredi.Ctx
