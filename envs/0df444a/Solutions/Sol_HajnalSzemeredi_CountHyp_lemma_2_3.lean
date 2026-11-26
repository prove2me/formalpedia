-- Prove2me | solution 1 for HajnalSzemeredi.CountHyp.lemma_2_3
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T22:48:15.803993+00:00
-- url     : https://prove2.me/submissions/90fb7871-7e85-4666-ba80-51ef90f169ff

module
public import Definitions.Def_HajnalSzemeredi_Defs
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Definitions.Def_HajnalSzemeredi_Count
public import Theorems.Thm_HajnalSzemeredi_CountHyp_card_Sy
public import Theorems.Thm_HajnalSzemeredi_CountHyp_deg_B
public import Theorems.Thm_HajnalSzemeredi_CountHyp_lemma_2_2
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
variable {V : Type*} {G : SimpleGraph V}
open HajnalSzemeredi.CountHyp
variable {S : Finset V} {c : V → ℕ} {PA PB TU : Finset ℕ} {r s : ℕ}
namespace HajnalSzemeredi.CountHyp
theorem _root_.solution (h : CountHyp G S c PA PB TU r s) :
    ∃ z ∈ S, c z ∈ TU ∧ (Sz G S c TU (part S c PB) z).Nonempty ∧
      ((∃ X ∈ PA, X ≠ c z ∧ Movable G S c z X) ∨
        ∃ y₁ ∈ Sz G S c TU (part S c PB) z, ∃ y₂ ∈ Sz G S c TU (part S c PB) z,
          y₁ ≠ y₂ ∧ ¬ G.Adj y₁ y₂) := by
  by_contra hcon
  have hnm : ∀ z ∈ S, c z ∈ TU → (Sz G S c TU (part S c PB) z).Nonempty →
      ∀ X ∈ PA, X ≠ c z → ¬ Movable G S c z X :=
    fun z hz hc hne X hX hXz hm => hcon ⟨z, hz, hc, hne, Or.inl ⟨X, hX, hXz, hm⟩⟩
  have hcl : ∀ z ∈ S, c z ∈ TU → ∀ y₁ ∈ Sz G S c TU (part S c PB) z,
      ∀ y₂ ∈ Sz G S c TU (part S c PB) z, y₁ ≠ y₂ → G.Adj y₁ y₂ :=
    fun z hz hc y₁ h₁ y₂ h₂ hne =>
      by_contra fun ha => hcon ⟨z, hz, hc, ⟨y₁, h₁⟩, Or.inr ⟨y₁, h₁, y₂, h₂, hne, ha⟩⟩
  obtain ⟨W, hW⟩ := h.ne
  obtain ⟨hq, -⟩ := h.lemma_2_2 hW fun z hz hne X hX hXW =>
    hnm z (mem_cls.1 hz).1 ((mem_cls.1 hz).2 ▸ hW) hne X hX (by rw [(mem_cls.1 hz).2]; exact hXW)
  have hswap : ∑ y ∈ part S c PB, ∑ z ∈ Sy G S c TU (part S c PB) y,
      ((PB.card : ℚ) / (Sz G S c TU (part S c PB) z).card) =
      ∑ z ∈ S.filter (fun z => c z ∈ TU), ∑ y ∈ Sz G S c TU (part S c PB) z,
        ((PB.card : ℚ) / (Sz G S c TU (part S c PB) z).card) := by
    apply sum_comm'
    intro y z
    simp only [Sy, Sz, mem_filter]
    constructor
    · rintro ⟨hy, hzS, hs⟩
      exact ⟨⟨hy, hs⟩, hzS, hs.2.1⟩
    · rintro ⟨⟨hy, hs⟩, hzS, _⟩
      exact ⟨hy, hzS, hs⟩
  have hup : ∑ z ∈ S.filter (fun z => c z ∈ TU), ∑ y ∈ Sz G S c TU (part S c PB) z,
      ((PB.card : ℚ) / (Sz G S c TU (part S c PB) z).card) ≤
      ∑ z ∈ S.filter (fun z => c z ∈ TU), (PB.card : ℚ) := by
    apply sum_le_sum
    intro z _
    rw [sum_const, nsmul_eq_mul]
    rcases Nat.eq_zero_or_pos (Sz G S c TU (part S c PB) z).card with h0 | h0
    · rw [h0]; simp
    · apply le_of_eq
      have : ((Sz G S c TU (part S c PB) z).card : ℚ) ≠ 0 := by positivity
      field_simp
  have hA' : (S.filter fun z => c z ∈ TU).card = TU.card * s := by
    rw [card_eq_sum_card_fiberwise (f := c) (s := S.filter fun z => c z ∈ TU) (t := TU)
      (fun z hz => (mem_filter.1 hz).2)]
    rw [sum_congr rfl (g := fun _ => s)]
    · simp
    intro X hX
    rw [← h.size X hX]
    congr 1
    ext z
    simp only [mem_filter, mem_cls]
    constructor
    · rintro ⟨⟨a, _⟩, b⟩; exact ⟨a, b⟩
    · rintro ⟨a, b⟩; exact ⟨⟨a, b ▸ hX⟩, b⟩
  have hlo : ∀ y ∈ part S c PB, (TU.card : ℚ) ≤ ∑ z ∈ Sy G S c TU (part S c PB) y,
      ((PB.card : ℚ) / (Sz G S c TU (part S c PB) z).card) := by
    intro y hy
    have hSy := h.card_Sy hy
    have hdB := h.deg_B hy
    have hle : ∀ z ∈ Sy G S c TU (part S c PB) y, (Sz G S c TU (part S c PB) z).card ≤
        (nbr G (part S c PB) y).card + 1 ∧ 0 < (Sz G S c TU (part S c PB) z).card := by
      intro z hz
      obtain ⟨hzS, hs⟩ := mem_filter.1 hz
      have hyz : y ∈ Sz G S c TU (part S c PB) z := mem_filter.2 ⟨hy, hs⟩
      refine ⟨?_, card_pos.2 ⟨y, hyz⟩⟩
      have hsub : Sz G S c TU (part S c PB) z ⊆ insert y (nbr G (part S c PB) y) := by
        intro y' hy'
        by_cases e : y' = y
        · rw [e]; exact mem_insert_self _ _
        · exact mem_insert_of_mem (mem_nbr.2 ⟨(mem_filter.1 hy').1,
            hcl z hzS hs.2.1 y hyz y' hy' (Ne.symm e)⟩)
      exact (card_le_card hsub).trans (card_insert_le _ _)
    have hSyq : (TU.card : ℚ) + 1 + (nbr G (part S c PB) y).card ≤
        (Sy G S c TU (part S c PB) y).card + PB.card := by exact_mod_cast hSy
    have hdBq : ((nbr G (part S c PB) y).card : ℚ) + 1 ≤ PB.card := by exact_mod_cast hdB
    have hqq : (PB.card : ℚ) + 1 ≤ TU.card := by exact_mod_cast hq
    calc (TU.card : ℚ) ≤ (Sy G S c TU (part S c PB) y).card *
          ((PB.card : ℚ) / ((nbr G (part S c PB) y).card + 1)) := by
          rw [mul_div_assoc', le_div_iff₀ (by positivity)]
          nlinarith [mul_nonneg (show (0:ℚ) ≤ TU.card - PB.card by linarith)
            (show (0:ℚ) ≤ PB.card - ((nbr G (part S c PB) y).card + 1) by linarith),
            mul_le_mul_of_nonneg_right hSyq (Nat.cast_nonneg (α := ℚ) PB.card)]
      _ = ∑ z ∈ Sy G S c TU (part S c PB) y,
          ((PB.card : ℚ) / ((nbr G (part S c PB) y).card + 1)) := by
          rw [sum_const, nsmul_eq_mul]
      _ ≤ _ := sum_le_sum fun z hz => div_le_div_of_nonneg_left (by positivity)
          (by exact_mod_cast (hle z hz).2) (by exact_mod_cast (hle z hz).1)
  have hL : (TU.card : ℚ) * (part S c PB).card ≤ ∑ y ∈ part S c PB,
      ∑ z ∈ Sy G S c TU (part S c PB) y,
        ((PB.card : ℚ) / (Sz G S c TU (part S c PB) z).card) := by
    calc _ = ∑ y ∈ part S c PB, (TU.card : ℚ) := by rw [sum_const, nsmul_eq_mul, mul_comm]
      _ ≤ _ := sum_le_sum hlo
  rw [hswap] at hL
  have key := hL.trans hup
  rw [sum_const, nsmul_eq_mul, hA', h.card_B] at key
  push_cast at key
  have : (1 : ℚ) ≤ TU.card := by exact_mod_cast (show 1 ≤ TU.card by omega)
  nlinarith
end HajnalSzemeredi.CountHyp
