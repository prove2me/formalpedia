-- Prove2me | solution 1 for JohnsonApprox.MaxSatWeighted.left_weight_nonincreasing
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-28T20:35:37.579632+00:00
-- url     : https://prove2.me/submissions/16602677-c606-4614-b14d-404213d2ec51

import Mathlib
import Definitions.Def_JohnsonApprox_Shared_Problem
import Definitions.Def_JohnsonApprox_MaxSatWeighted_B2
import Definitions.Def_JohnsonApprox_MaxSatWeighted_ExampleK3



namespace JohnsonApprox.MaxSatWeighted

open Finset Shared

lemma neg_neg' (l : Literal) : l.neg.neg = l := by
  cases l with | mk v p => simp [Literal.neg]

lemma same_var (l l' : Literal) (h : l'.var = l.var) : l' = l ∨ l' = l.neg := by
  cases l with | mk v p =>
  cases l' with | mk v' p' =>
  simp only [Literal.neg, Literal.mk.injEq] at h ⊢
  subst h
  cases p <;> cases p' <;> simp

/-- number of decided literals of a clause -/
def ndec (D : Finset ℕ) (C : Clause) : ℕ := (C.filter (fun l => l.var ∈ D)).card

lemma ndec_insert (D : Finset ℕ) (C : Clause) (y : Literal) (hy : y.var ∉ D) (hyC : y ∉ C) :
    ndec (insert y.var D) C = ndec D C + if y.neg ∈ C then 1 else 0 := by
  unfold ndec
  have : C.filter (fun l => l.var ∈ insert y.var D) =
      C.filter (fun l => l.var ∈ D) ∪ C.filter (fun l => l = y.neg) := by
    ext l
    simp only [mem_filter, mem_insert, mem_union]
    constructor
    · rintro ⟨hl, h | h⟩
      · right; refine ⟨hl, ?_⟩
        rcases same_var y l h with rfl | rfl
        · exact absurd hl hyC
        · rfl
      · left; exact ⟨hl, h⟩
    · rintro (⟨hl, h⟩ | ⟨hl, rfl⟩)
      · exact ⟨hl, Or.inr h⟩
      · exact ⟨hl, Or.inl rfl⟩
  rw [this, card_union_of_disjoint]
  · rw [filter_eq' C]; split_ifs <;> simp
  · rw [disjoint_left]; intro l h1 h2
    simp only [mem_filter] at h1 h2
    rw [h2.2] at h1; exact hy h1.2

lemma inv (S : Finset Clause) (σ : State) (hσ : Reachable S σ) :
    Disjoint σ.SUB σ.LEFT ∧ σ.SUB ∪ σ.LEFT = S ∧ (∀ l ∈ σ.TRUE, l.var ∈ σ.decided) ∧
      (∀ v ∈ σ.decided, ∃ l ∈ σ.TRUE, l.var = v) ∧ (∀ C ∈ σ.LEFT, ∀ l ∈ C, l ∉ σ.TRUE) ∧
      (∀ C ∈ σ.LEFT, σ.w C = 2 ^ ndec σ.decided C / 2 ^ C.card) := by
  induction hσ with
  | refl =>
    refine ⟨disjoint_empty_left _, empty_union _, by simp [init], by simp [init], by simp [init], ?_⟩
    intro C _; simp [init, ndec]
  | @tail σ₁ σ₂ _ hstep ih =>
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := ih
    obtain ⟨y, _, hyLIT, _, rfl⟩ := hstep
    have hyd : y.var ∉ σ₁.decided := hyLIT
    have hyT : y ∉ σ₁.TRUE := fun hy => hyLIT (h3 y hy)
    have hnyT : y.neg ∉ σ₁.TRUE := fun hy => hyLIT (h3 y.neg hy)
    unfold State.update
    split_ifs with hw
    · have hYTsub : σ₁.YT y ⊆ σ₁.LEFT := filter_subset _ _
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · show Disjoint (σ₁.SUB ∪ σ₁.YT y) (σ₁.LEFT \ σ₁.YT y)
        rw [disjoint_union_left]
        exact ⟨disjoint_of_subset_right sdiff_subset h1, disjoint_sdiff⟩
      · show σ₁.SUB ∪ σ₁.YT y ∪ (σ₁.LEFT \ σ₁.YT y) = S
        rw [union_assoc, union_sdiff_of_subset hYTsub, h2]
      · intro l hl
        rcases mem_insert.1 hl with rfl | hl
        · exact mem_insert_self _ _
        · exact mem_insert_of_mem (h3 l hl)
      · intro v hv
        rcases mem_insert.1 hv with rfl | hv
        · exact ⟨y, mem_insert_self _ _, rfl⟩
        · obtain ⟨l, hl, hlv⟩ := h4 v hv
          exact ⟨l, mem_insert_of_mem hl, hlv⟩
      · intro C hC l hl hlT
        rw [mem_sdiff] at hC
        rcases mem_insert.1 hlT with rfl | hlT
        · exact hC.2 (mem_filter.2 ⟨hC.1, hl⟩)
        · exact h5 C hC.1 l hl hlT
      · intro C hC
        rw [mem_sdiff] at hC
        have hyC : y ∉ C := fun h => hC.2 (mem_filter.2 ⟨hC.1, h⟩)
        show doubleOn σ₁.w (σ₁.YF y) C = 2 ^ ndec (insert y.var σ₁.decided) C / 2 ^ C.card
        rw [ndec_insert _ _ _ hyd hyC, doubleOn, h6 C hC.1]
        by_cases hn : y.neg ∈ C
        · have hm : C ∈ σ₁.YF y := by unfold State.YF; exact mem_filter.2 ⟨hC.1, hn⟩
          rw [if_pos hm, if_pos hn, pow_succ]; ring
        · have hm : C ∉ σ₁.YF y := by unfold State.YF; exact fun h => hn (mem_filter.1 h).2
          rw [if_neg hm, if_neg hn, add_zero]
    · have hYFsub : σ₁.YF y ⊆ σ₁.LEFT := filter_subset _ _
      have hyd' : y.neg.var ∉ σ₁.decided := hyd
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · show Disjoint (σ₁.SUB ∪ σ₁.YF y) (σ₁.LEFT \ σ₁.YF y)
        rw [disjoint_union_left]
        exact ⟨disjoint_of_subset_right sdiff_subset h1, disjoint_sdiff⟩
      · show σ₁.SUB ∪ σ₁.YF y ∪ (σ₁.LEFT \ σ₁.YF y) = S
        rw [union_assoc, union_sdiff_of_subset hYFsub, h2]
      · intro l hl
        rcases mem_insert.1 hl with rfl | hl
        · exact mem_insert_self _ _
        · exact mem_insert_of_mem (h3 l hl)
      · intro v hv
        rcases mem_insert.1 hv with rfl | hv
        · exact ⟨y.neg, mem_insert_self _ _, rfl⟩
        · obtain ⟨l, hl, hlv⟩ := h4 v hv
          exact ⟨l, mem_insert_of_mem hl, hlv⟩
      · intro C hC l hl hlT
        rw [mem_sdiff] at hC
        rcases mem_insert.1 hlT with rfl | hlT
        · exact hC.2 (mem_filter.2 ⟨hC.1, hl⟩)
        · exact h5 C hC.1 l hl hlT
      · intro C hC
        rw [mem_sdiff] at hC
        have hyC : y.neg ∉ C := fun h => hC.2 (mem_filter.2 ⟨hC.1, h⟩)
        show doubleOn σ₁.w (σ₁.YT y) C = 2 ^ ndec (insert y.var σ₁.decided) C / 2 ^ C.card
        rw [show y.var = y.neg.var from rfl, ndec_insert _ _ _ hyd' hyC, neg_neg', doubleOn,
          h6 C hC.1]
        by_cases hn : y ∈ C
        · have hm : C ∈ σ₁.YT y := by unfold State.YT; exact mem_filter.2 ⟨hC.1, hn⟩
          rw [if_pos hm, if_pos hn, pow_succ]; ring
        · have hm : C ∉ σ₁.YT y := by unfold State.YT; exact fun h => hn (mem_filter.1 h).2
          rw [if_neg hm, if_neg hn, add_zero]

theorem initial_weight_core (k : ℕ) (S : Finset Shared.Clause) (hS : Shared.InMS k S) :
    (init S).weight (init S).LEFT ≤ (S.card : ℚ) / 2 ^ k := by
  unfold State.weight init
  simp only
  rw [div_eq_mul_one_div, ← nsmul_eq_mul, ← sum_const]
  apply sum_le_sum; intro C hC
  apply one_div_le_one_div_of_le (by positivity)
  exact pow_le_pow_right₀ (by norm_num) (hS C hC)

lemma w_nonneg (S : Finset Clause) (σ : State) (hσ : Reachable S σ) :
    ∀ C ∈ σ.LEFT, 0 ≤ σ.w C := by
  intro C hC; rw [(inv S σ hσ).2.2.2.2.2 C hC]; positivity

lemma step_weight (S : Finset Clause) (σ σ' : State) (hσ : Reachable S σ) (hst : Step σ σ') :
    σ'.weight σ'.LEFT ≤ σ.weight σ.LEFT := by
  obtain ⟨y, _, _, _, rfl⟩ := hst
  have hw0 := w_nonneg S σ hσ
  unfold State.update
  split_ifs with hw
  · show ∑ C ∈ σ.LEFT \ σ.YT y, doubleOn σ.w (σ.YF y) C ≤ ∑ C ∈ σ.LEFT, σ.w C
    have e : ∀ C ∈ σ.LEFT \ σ.YT y, doubleOn σ.w (σ.YF y) C =
        σ.w C + if C ∈ σ.YF y then σ.w C else 0 := by
      intro C _; unfold doubleOn; split_ifs <;> ring
    rw [sum_congr rfl e, sum_add_distrib, ← sum_filter]
    have h1 : ∑ C ∈ σ.LEFT \ σ.YT y, σ.w C = ∑ C ∈ σ.LEFT, σ.w C - ∑ C ∈ σ.YT y, σ.w C := by
      have hsub : σ.YT y ⊆ σ.LEFT := filter_subset _ _
      rw [sum_sdiff_eq_sub hsub]
    have h2 : ∑ C ∈ (σ.LEFT \ σ.YT y).filter (fun C => C ∈ σ.YF y), σ.w C ≤
        ∑ C ∈ σ.YF y, σ.w C := by
      apply sum_le_sum_of_subset_of_nonneg
      · intro C hC; exact (mem_filter.1 hC).2
      · intro C hC _; exact hw0 C (by unfold State.YF State.YT at *; exact filter_subset _ _ hC)
    unfold State.weight at hw
    linarith
  · show ∑ C ∈ σ.LEFT \ σ.YF y, doubleOn σ.w (σ.YT y) C ≤ ∑ C ∈ σ.LEFT, σ.w C
    have e : ∀ C ∈ σ.LEFT \ σ.YF y, doubleOn σ.w (σ.YT y) C =
        σ.w C + if C ∈ σ.YT y then σ.w C else 0 := by
      intro C _; unfold doubleOn; split_ifs <;> ring
    rw [sum_congr rfl e, sum_add_distrib, ← sum_filter]
    have h1 : ∑ C ∈ σ.LEFT \ σ.YF y, σ.w C = ∑ C ∈ σ.LEFT, σ.w C - ∑ C ∈ σ.YF y, σ.w C := by
      have hsub : σ.YF y ⊆ σ.LEFT := filter_subset _ _
      rw [sum_sdiff_eq_sub hsub]
    have h2 : ∑ C ∈ (σ.LEFT \ σ.YF y).filter (fun C => C ∈ σ.YT y), σ.w C ≤
        ∑ C ∈ σ.YT y, σ.w C := by
      apply sum_le_sum_of_subset_of_nonneg
      · intro C hC; exact (mem_filter.1 hC).2
      · intro C hC _; exact hw0 C (by unfold State.YF State.YT at *; exact filter_subset _ _ hC)
    unfold State.weight at hw
    push_neg at hw
    linarith

theorem left_weight_core (k : ℕ) (S : Finset Shared.Clause) (hS : Shared.InMS k S) :
    (∀ σ σ' : State, Reachable S σ → Step σ σ' → σ'.weight σ'.LEFT ≤ σ.weight σ.LEFT) ∧
    (∀ σ : State, Reachable S σ → σ.weight σ.LEFT ≤ (S.card : ℚ) / 2 ^ k) := by
  refine ⟨fun σ σ' hσ hst => step_weight S σ σ' hσ hst, ?_⟩
  intro σ hσ
  induction hσ with
  | refl => exact initial_weight_core k S hS
  | @tail σ₁ σ₂ hr hst ih => exact (step_weight S σ₁ σ₂ hr hst).trans ih

theorem halt_dead_core (S : Finset Shared.Clause) (σ : State) (hσ : Reachable S σ)
    (hhalt : Halts σ) : ∀ C ∈ σ.LEFT, σ.w C = 1 := by
  intro C hC
  rw [(inv S σ hσ).2.2.2.2.2 C hC]
  have : ndec σ.decided C = C.card := by
    unfold ndec
    rw [filter_true_of_mem]
    intro l hl
    have := hhalt C hC l hl
    unfold State.inLIT at this; push_neg at this; exact this
  rw [this, div_self (by positivity)]

theorem halt_sub_core (k : ℕ) (S : Finset Shared.Clause) (hS : Shared.InMS k S) (σ : State)
    (hσ : Reachable S σ) (hhalt : Halts σ) :
    2 ^ k * σ.LEFT.card ≤ S.card ∧ (2 ^ k - 1) * S.card ≤ 2 ^ k * σ.SUB.card := by
  obtain ⟨h1, h2, _⟩ := inv S σ hσ
  have hW := (left_weight_core k S hS).2 σ hσ
  have hone := halt_dead_core S σ hσ hhalt
  have hWL : σ.weight σ.LEFT = σ.LEFT.card := by
    unfold State.weight; rw [sum_congr rfl hone]; simp
  rw [hWL, le_div_iff₀ (by positivity)] at hW
  have hL : 2 ^ k * σ.LEFT.card ≤ S.card := by
    have : ((σ.LEFT.card * 2 ^ k : ℕ) : ℚ) ≤ (S.card : ℚ) := by push_cast; exact hW
    have := Nat.cast_le.1 this; linarith [mul_comm (σ.LEFT.card) (2 ^ k)]
  have hc := card_union_of_disjoint h1
  rw [h2] at hc
  refine ⟨hL, ?_⟩
  have hp : 1 ≤ 2 ^ k := Nat.one_le_two_pow
  zify [hp]
  have : ((2 : ℤ) ^ k) * (σ.LEFT.card : ℤ) ≤ S.card := by exact_mod_cast hL
  have hc' : (S.card : ℤ) = σ.SUB.card + σ.LEFT.card := by exact_mod_cast hc
  nlinarith

end JohnsonApprox.MaxSatWeighted

open JohnsonApprox JohnsonApprox.MaxSatWeighted

theorem solution (k : ℕ) (S : Finset Shared.Clause) (hS : Shared.InMS k S) :
    (∀ σ σ' : State, Reachable S σ → Step σ σ' → σ'.weight σ'.LEFT ≤ σ.weight σ.LEFT) ∧
    (∀ σ : State, Reachable S σ → σ.weight σ.LEFT ≤ (S.card : ℚ) / 2 ^ k) := by
  exact left_weight_core k S hS
