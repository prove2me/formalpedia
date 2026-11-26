-- Prove2me | solution 1 for HajnalSzemeredi.shift_of_acc
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T22:48:15.210803+00:00
-- url     : https://prove2.me/submissions/fad1a6b0-e756-4105-a2df-f24f99a66f20

module
public import Definitions.Def_HajnalSzemeredi_Defs
public import Definitions.Def_HajnalSzemeredi_Reach
public import Definitions.Def_HajnalSzemeredi_Shift
public import Theorems.Thm_HajnalSzemeredi_shift
public import Theorems.Thm_HajnalSzemeredi_mem_cls
attribute [local simp] HajnalSzemeredi.mem_cls



set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open Classical Finset Relation
open HajnalSzemeredi
variable {V : Type*} {G : SimpleGraph V}
namespace HajnalSzemeredi
theorem _root_.solution {S : Finset V} {P : Finset ℕ} {c : V → ℕ} {s lo hi : ℕ}
    (hc : IsNear G S P c s lo hi) (hacc : ReflTransGen (Mov G S c) hi lo) :
    ∃ c', IsEq G S P c' s := by
  set K : Finset ℕ := insert lo (S.image c)
  have key : ∀ a, ReflTransGen (Mov G S c) a lo →
      a ∈ K ∧ ReflTransGen (fun a b => Mov G S c a b ∧ a ∈ K ∧ b ∈ K) a lo := by
    intro a h
    induction h using ReflTransGen.head_induction_on with
    | refl => exact ⟨mem_insert_self _ _, ReflTransGen.refl⟩
    | head hab _ ih =>
      obtain ⟨v, hv, -⟩ := id hab
      rw [mem_cls] at hv
      have haK : _ ∈ K := mem_insert_of_mem (mem_image.mpr ⟨v, hv.1, hv.2⟩)
      exact ⟨haK, ReflTransGen.head ⟨hab, haK, ih.1⟩ ih.2⟩
  exact shift K c hi hc (key hi hacc).2
end HajnalSzemeredi
