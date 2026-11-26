-- Prove2me | solution 1 for HajnalSzemeredi.Ctx.card_r
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T22:45:51.851723+00:00
-- url     : https://prove2.me/submissions/b65c06a7-4cf0-4f21-bb04-1efc771fe956

module
public import Definitions.Def_HajnalSzemeredi_Count
public import Definitions.Def_HajnalSzemeredi_Reach
public import Mathlib.Combinatorics.Enumerative.DoubleCounting
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Tactic.Ring
public import Definitions.Def_HajnalSzemeredi_Structure
public import Theorems.Thm_HajnalSzemeredi_Ctx_acc_subset

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
theorem _root_.solution (h : Ctx G S P c r s lo hi) :
    r + 1 = (acc G S P c lo).card + (P \ acc G S P c lo).card := by
  have h1 := card_sdiff_of_subset (acc_subset (G := G) (S := S) (P := P) (c := c) (lo := lo))
  have h2 := card_le_card (acc_subset (G := G) (S := S) (P := P) (c := c) (lo := lo))
  have h3 := h.card_P
  omega
end HajnalSzemeredi.Ctx
