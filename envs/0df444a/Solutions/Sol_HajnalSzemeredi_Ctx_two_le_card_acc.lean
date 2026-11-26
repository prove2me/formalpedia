-- Prove2me | solution 1 for HajnalSzemeredi.Ctx.two_le_card_acc
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T22:48:04.750865+00:00
-- url     : https://prove2.me/submissions/fb012755-621f-47d5-900e-8e6f2e5b73f8

module
public import Definitions.Def_HajnalSzemeredi_Count
public import Definitions.Def_HajnalSzemeredi_Reach
public import Mathlib.Combinatorics.Enumerative.DoubleCounting
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Tactic.Ring
public import Definitions.Def_HajnalSzemeredi_Structure
public import Theorems.Thm_HajnalSzemeredi_Ctx_lo_mem_acc
public import Theorems.Thm_HajnalSzemeredi_Ctx_card_r
public import Theorems.Thm_HajnalSzemeredi_Ctx_h21
public import Theorems.Thm_HajnalSzemeredi_Ctx_card_B
public import Theorems.Thm_HajnalSzemeredi_mem_cls
public import Theorems.Thm_HajnalSzemeredi_mem_nbr
attribute [local simp] HajnalSzemeredi.mem_cls
attribute [local simp] HajnalSzemeredi.mem_nbr



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
theorem _root_.solution (h : Ctx G S P c r s lo hi) : 2 ≤ (acc G S P c lo).card := by
  by_contra hlt
  push Not at hlt
  have hA : acc G S P c lo = {lo} := by
    refine eq_singleton_iff_unique_mem.mpr ⟨h.lo_mem_acc, fun x hx => ?_⟩
    by_contra hne
    have : ({x, lo} : Finset ℕ) ⊆ acc G S P c lo := by
      intro y hy
      rcases mem_insert.mp hy with rfl | hy
      · exact hx
      · rw [mem_singleton.mp hy]; exact h.lo_mem_acc
    have := card_le_card this
    rw [card_pair hne] at this
    omega
  set B := part S c (P \ acc G S P c lo)
  have hrB : (P \ acc G S P c lo).card = r := by
    have h1 := h.card_r
    have h2 : (acc G S P c lo).card = 1 := by rw [hA, card_singleton]
    omega
  -- doble conteo de aristas entre `B` y la clase `lo`
  have hdc := sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow (s := B) (t := cls S c lo)
    (r := fun y x => G.Adj y x)
  have hleft : B.card ≤ ∑ y ∈ B, ((cls S c lo).bipartiteAbove (fun y x => G.Adj y x) y).card := by
    rw [card_eq_sum_ones]
    refine sum_le_sum fun y hy => ?_
    obtain ⟨w, hw⟩ := h.h21 hy h.lo_mem_acc
    rw [nIn, mem_inter, mem_nbr] at hw
    exact card_pos.mpr ⟨w, mem_filter.mpr ⟨hw.2, hw.1.2⟩⟩
  have hright : ∑ x ∈ cls S c lo, (B.bipartiteBelow (fun y x => G.Adj y x) x).card ≤
      ∑ _x ∈ cls S c lo, r := by
    refine sum_le_sum fun x hx => ?_
    refine le_trans (card_le_card fun y hy => ?_) (h.deg x (mem_cls.mp hx).1)
    obtain ⟨hyB, hadj⟩ := mem_filter.mp hy
    exact mem_nbr.mpr ⟨(mem_filter.mp hyB).1, hadj.symm⟩
  rw [sum_const, smul_eq_mul] at hright
  have hB : B.card = r * s + 1 := by
    have := h.card_B
    rw [hrB] at this
    exact this
  have hlo := h.near.card_lo
  have hmul : (cls S c lo).card * r ≤ s * r := Nat.mul_le_mul_right r (by omega)
  have hcomm : r * s = s * r := Nat.mul_comm r s
  have e1 : B.card ≤ (cls S c lo).card * r := by
    calc B.card ≤ _ := hleft
      _ = _ := hdc
      _ ≤ _ := hright
  omega
end HajnalSzemeredi.Ctx
