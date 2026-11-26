-- Prove2me | solution 1 for HajnalSzemeredi.Ctx.T_lo_nonempty
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T22:48:42.209909+00:00
-- url     : https://prove2.me/submissions/ea9e5897-39c4-4614-b1e8-01711999f9fb

module
public import Definitions.Def_HajnalSzemeredi_Count
public import Definitions.Def_HajnalSzemeredi_Reach
public import Mathlib.Combinatorics.Enumerative.DoubleCounting
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Tactic.Ring
public import Definitions.Def_HajnalSzemeredi_Structure
public import Theorems.Thm_HajnalSzemeredi_Ctx_lo_mem_acc
public import Theorems.Thm_HajnalSzemeredi_Ctx_two_le_card_acc

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
theorem _root_.solution (h : Ctx G S P c r s lo hi) : (T G S P c lo lo).Nonempty := by
  have h2 := h.two_le_card_acc
  have : 1 < ((acc G S P c lo).erase lo).card + 1 := by
    rw [card_erase_add_one h.lo_mem_acc]; omega
  obtain ⟨X, hX⟩ := card_pos.mp (by omega : 0 < ((acc G S P c lo).erase lo).card)
  refine ⟨X, mem_filter.mpr ⟨hX, fun hpath => ?_⟩⟩
  have hXlo := (mem_erase.mp hX).1
  rcases hpath.cases_tail with h' | ⟨b, -, hb⟩
  · exact hXlo h'.symm
  · exact hb.2.2 rfl
end HajnalSzemeredi.Ctx
