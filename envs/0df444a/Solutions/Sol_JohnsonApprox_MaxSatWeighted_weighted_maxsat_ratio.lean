-- Prove2me | solution 1 for JohnsonApprox.MaxSatWeighted.weighted_maxsat_ratio
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-28T20:41:14.59178+00:00
-- url     : https://prove2.me/submissions/6e223125-4001-416e-9668-e3acc857a96e

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

def c1 : Clause := {lit 1, lit 2, lit 3}
def c2 : Clause := {nlit 1, lit 4, lit 5}
def c3 : Clause := {lit 1, nlit 2, lit 3}
def c4 : Clause := {nlit 1, lit 6, lit 7}
def c5 : Clause := {lit 1, lit 2, nlit 3}
def c6 : Clause := {nlit 1, lit 8, lit 9}
def c7 : Clause := {lit 1, nlit 2, nlit 3}
def c8 : Clause := {nlit 1, lit 10, lit 11}

lemma ex_eq : exampleK3 = {c1, c2, c3, c4, c5, c6, c7, c8} := rfl

lemma update_of_le (σ : State) (y : Literal) (h : σ.weight (σ.YF y) ≤ σ.weight (σ.YT y)) :
    σ.update y = ⟨σ.SUB ∪ σ.YT y, σ.LEFT \ σ.YT y, insert y σ.TRUE, insert y.var σ.decided,
      doubleOn σ.w (σ.YF y)⟩ := by
  unfold State.update; rw [if_pos h]

def w0 : Clause → ℚ := fun C => 1 / 2 ^ C.card
def σ0 : State := init exampleK3
def σ1 : State := ⟨{c1, c5}, {c2, c3, c4, c6, c7, c8}, {lit 2}, {2}, doubleOn w0 {c3, c7}⟩
def σ2 : State := ⟨{c1, c5, c3}, {c2, c4, c6, c7, c8}, {lit 3, lit 2}, {3, 2},
  doubleOn (doubleOn w0 {c3, c7}) {c7}⟩
def σ3 : State := ⟨{c1, c5, c3, c2, c4, c6, c8}, {c7}, {nlit 1, lit 3, lit 2}, {1, 3, 2},
  doubleOn (doubleOn (doubleOn w0 {c3, c7}) {c7}) {c7}⟩

lemma yt1 : σ0.YT (lit 2) = {c1, c5} := by decide
lemma yf1 : σ0.YF (lit 2) = {c3, c7} := by decide

lemma yt2 : σ1.YT (lit 3) = {c3} := by decide
lemma yf2 : σ1.YF (lit 3) = {c7} := by decide
lemma yt3 : σ2.YT (nlit 1) = {c2, c4, c6, c8} := by decide
lemma yf3 : σ2.YF (nlit 1) = {c7} := by decide

lemma cards : c1.card = 3 ∧ c2.card = 3 ∧ c3.card = 3 ∧ c4.card = 3 ∧ c5.card = 3 ∧
    c6.card = 3 ∧ c7.card = 3 ∧ c8.card = 3 := by decide

lemma step1 : StepWith σ0 (lit 2) σ1 := by
  have hle : σ0.weight (σ0.YF (lit 2)) ≤ σ0.weight (σ0.YT (lit 2)) := by
    rw [yf1, yt1]; unfold State.weight
    rw [sum_pair (by decide), sum_pair (by decide)]
    simp only [σ0, init, cards]; norm_num
  refine ⟨by unfold Halts State.inLIT σ0 init; decide, by unfold State.inLIT σ0 init; decide,
    by unfold σ0 init; decide, ?_⟩
  rw [update_of_le σ0 (lit 2) hle, yt1, yf1]
  simp only [σ1, State.mk.injEq]
  refine ⟨by decide, by decide, by decide, by decide, by first | rfl | trivial⟩

lemma step2 : StepWith σ1 (lit 3) σ2 := by
  have hle : σ1.weight (σ1.YF (lit 3)) ≤ σ1.weight (σ1.YT (lit 3)) := by
    rw [yf2, yt2]; unfold State.weight
    simp only [sum_singleton, σ1, doubleOn, w0, cards]
    rw [if_pos (by decide), if_pos (by decide)]
  refine ⟨by unfold Halts State.inLIT σ1; decide, by unfold State.inLIT σ1; decide,
    by unfold σ1; decide, ?_⟩
  rw [update_of_le σ1 (lit 3) hle, yt2, yf2]
  simp only [σ1, σ2, State.mk.injEq]
  refine ⟨by decide, by decide, by decide, by decide, by first | rfl | trivial⟩

lemma step3 : StepWith σ2 (nlit 1) σ3 := by
  have hle : σ2.weight (σ2.YF (nlit 1)) ≤ σ2.weight (σ2.YT (nlit 1)) := by
    rw [yf3, yt3]; unfold State.weight
    rw [sum_insert (by decide), sum_insert (by decide), sum_pair (by decide)]
    simp only [sum_singleton, σ2, doubleOn, w0, cards]
    rw [if_pos (by decide), if_pos (by decide), if_neg (by decide), if_neg (by decide),
      if_neg (by decide), if_neg (by decide), if_neg (by decide), if_neg (by decide),
      if_neg (by decide), if_neg (by decide)]
    norm_num
  refine ⟨by unfold Halts State.inLIT σ2; decide, by unfold State.inLIT σ2; decide,
    by unfold σ2; decide, ?_⟩
  rw [update_of_le σ2 (nlit 1) hle, yt3, yf3]
  simp only [σ2, σ3, State.mk.injEq]
  refine ⟨by decide, by decide, by decide, by decide, by first | rfl | trivial⟩

lemma opt_le_card (S : Finset Clause) : opt S ≤ S.card := by
  unfold opt
  apply Finset.sup'_le
  intro S' hS'
  unfold solutions at hS'
  simp only [Finset.mem_filter, Finset.mem_powerset] at hS'
  exact card_le_card hS'.1

lemma card_le_opt (S : Finset Clause) (hsat : Satisfiable S) : S.card ≤ opt S := by
  unfold opt
  exact Finset.le_sup' Finset.card (by
    unfold solutions; simp only [Finset.mem_filter, Finset.mem_powerset]
    exact ⟨subset_refl _, hsat⟩)

theorem exampleK3_core :
    Shared.InMS 3 exampleK3 ∧ Shared.opt exampleK3 = 8 ∧ ∃ X, Choosable exampleK3 X ∧ X.card = 7 := by
  have hcard : exampleK3.card = 8 := by decide
  refine ⟨?_, ?_, ?_⟩
  · intro C hC
    have : ∀ C ∈ exampleK3, 3 ≤ C.card := by decide
    exact this C hC
  · apply le_antisymm (hcard ▸ opt_le_card _)
    rw [← hcard]
    apply card_le_opt
    refine ⟨⟨{l | l.pos = true}, fun l hl hneg => ?_⟩, fun C hC => ?_⟩
    · simp only [Set.mem_setOf_eq, Literal.neg] at hl hneg
      rw [hl] at hneg; exact Bool.noConfusion hneg
    · have : ∀ C ∈ exampleK3, ∃ l ∈ C, l.pos = true := by decide
      obtain ⟨l, hl, hp⟩ := this C hC
      exact ⟨l, hl, hp⟩
  · refine ⟨σ3.SUB, ⟨σ3, ?_, ?_, rfl⟩, by decide⟩
    · exact ((Relation.ReflTransGen.refl.tail ⟨_, step1⟩).tail ⟨_, step2⟩).tail ⟨_, step3⟩
    · unfold Halts State.inLIT σ3; decide


/-! ### A tight family for every `k ≥ 2` -/

def cstar (k : ℕ) : Clause := (range k).image nlit
def fr (k j m t : ℕ) : Literal := ⟨k + Nat.pair (Nat.pair j m) t, true⟩
def Bc (k j m : ℕ) : Clause := insert (lit j) ((range (k - 1)).image (fr k j m))
def blocks (k j : ℕ) : Finset Clause := (range (2 ^ j)).image (Bc k j)
def Sw (k : ℕ) : Finset Clause := insert (cstar k) ((range k).biUnion (blocks k))

lemma mem_Bc {k j m : ℕ} {l : Literal} : l ∈ Bc k j m ↔ l = lit j ∨ ∃ t < k - 1, l = fr k j m t := by
  unfold Bc; simp only [mem_insert, mem_image, mem_range]
  constructor
  · rintro (h | ⟨t, ht, rfl⟩)
    · exact Or.inl h
    · exact Or.inr ⟨t, ht, rfl⟩
  · rintro (h | ⟨t, ht, rfl⟩)
    · exact Or.inl h
    · exact Or.inr ⟨t, ht, rfl⟩

lemma Bc_pos {k j m : ℕ} {l : Literal} (h : l ∈ Bc k j m) : l.pos = true := by
  rcases mem_Bc.1 h with rfl | ⟨t, _, rfl⟩ <;> rfl

lemma lit_mem_Bc {k j j' m : ℕ} (hj : j < k) : lit j ∈ Bc k j' m ↔ j = j' := by
  rw [mem_Bc]
  constructor
  · rintro (h | ⟨t, _, h⟩)
    · simp only [lit, Literal.mk.injEq, and_true] at h; exact h
    · simp only [lit, fr, Literal.mk.injEq, and_true] at h; omega
  · rintro rfl; exact Or.inl rfl

lemma nlit_not_Bc {k j j' m : ℕ} : nlit j ∉ Bc k j' m := fun h => by
  have := Bc_pos h; simp [nlit] at this

lemma mem_cstar {k : ℕ} {l : Literal} : l ∈ cstar k ↔ ∃ i < k, l = nlit i := by
  unfold cstar; simp only [mem_image, mem_range]
  constructor
  · rintro ⟨i, hi, rfl⟩; exact ⟨i, hi, rfl⟩
  · rintro ⟨i, hi, rfl⟩; exact ⟨i, hi, rfl⟩

lemma cstar_ne_Bc (k j m : ℕ) (hk : 1 ≤ k) : cstar k ≠ Bc k j m := by
  intro h
  have : nlit 0 ∈ cstar k := mem_cstar.2 ⟨0, by omega, rfl⟩
  rw [h] at this; exact nlit_not_Bc this

lemma Bc_inj {k j j' m m' : ℕ} (hk : 2 ≤ k) (hj : j < k) (hj' : j' < k)
    (h : Bc k j m = Bc k j' m') : j = j' ∧ m = m' := by
  have e1 : j = j' := by
    have : lit j ∈ Bc k j m := mem_Bc.2 (Or.inl rfl)
    rw [h] at this; exact (lit_mem_Bc hj).1 this
  subst e1
  refine ⟨rfl, ?_⟩
  have : fr k j m 0 ∈ Bc k j m := mem_Bc.2 (Or.inr ⟨0, by omega, rfl⟩)
  rw [h, mem_Bc] at this
  rcases this with h1 | ⟨t, _, h1⟩
  · simp only [fr, lit, Literal.mk.injEq, and_true] at h1; omega
  · simp only [fr, Literal.mk.injEq, and_true, add_right_inj] at h1
    exact (Nat.pair_eq_pair.1 (Nat.pair_eq_pair.1 h1).1).2

lemma mem_blocks {k j : ℕ} {C : Clause} : C ∈ blocks k j ↔ ∃ m < 2 ^ j, C = Bc k j m := by
  unfold blocks; simp only [mem_image, mem_range]
  constructor
  · rintro ⟨m, hm, rfl⟩; exact ⟨m, hm, rfl⟩
  · rintro ⟨m, hm, rfl⟩; exact ⟨m, hm, rfl⟩

lemma blocks_disj (k : ℕ) (hk : 2 ≤ k) (i j : ℕ) (hi : i < k) (hj : j < k) (hij : i ≠ j) :
    Disjoint (blocks k i) (blocks k j) := by
  rw [disjoint_left]
  intro C h1 h2
  obtain ⟨m, _, rfl⟩ := mem_blocks.1 h1
  obtain ⟨m', _, h⟩ := mem_blocks.1 h2
  exact hij (Bc_inj hk hi hj h).1

lemma card_blocks (k j : ℕ) (hk : 2 ≤ k) (hj : j < k) : (blocks k j).card = 2 ^ j := by
  unfold blocks
  rw [card_image_of_injOn, card_range]
  intro m _ m' _ h; exact (Bc_inj hk hj hj h).2

lemma card_Bc (k j m : ℕ) (hj : j < k) : (Bc k j m).card = k := by
  unfold Bc
  rw [card_insert_of_notMem, card_image_of_injective, card_range]
  · omega
  · intro t t' h
    simp only [fr, Literal.mk.injEq, add_right_inj, and_true] at h
    exact (Nat.pair_eq_pair.1 h).2
  · simp only [mem_image, mem_range, not_exists, not_and]
    intro t _ h; simp only [fr, lit, Literal.mk.injEq, and_true] at h; omega

lemma card_cstar (k : ℕ) : (cstar k).card = k := by
  unfold cstar; rw [card_image_of_injective, card_range]
  intro a b h; simpa [nlit] using h

lemma mem_bU {k : ℕ} (s : Finset ℕ) (C : Clause) :
    C ∈ s.biUnion (blocks k) ↔ ∃ j ∈ s, ∃ m < 2 ^ j, C = Bc k j m := by
  simp only [mem_biUnion, mem_blocks]

def wj (k j : ℕ) : Clause → ℚ := fun C => if C = cstar k then 2 ^ j / 2 ^ k else 1 / 2 ^ C.card

def st (k j : ℕ) : State :=
  ⟨(range j).biUnion (blocks k), insert (cstar k) ((Ico j k).biUnion (blocks k)),
    (range j).image lit, range j, wj k j⟩

lemma st_zero (k : ℕ) : st k 0 = init (Sw k) := by
  unfold st init Sw
  simp only [range_zero, biUnion_empty, image_empty, State.mk.injEq, true_and]
  refine ⟨by rw [range_eq_Ico], ?_⟩
  funext C; unfold wj
  split_ifs with h
  · subst h; rw [card_cstar]; ring
  · rfl

lemma st_step (k j : ℕ) (hk : 2 ≤ k) (hj : j < k) : StepWith (st k j) (lit j) (st k (j + 1)) := by
  have hYT : (st k j).YT (lit j) = blocks k j := by
    ext C
    simp only [State.YT, st, mem_filter, mem_insert, mem_bU, mem_Ico]
    constructor
    · rintro ⟨h | ⟨i, hi, m, hm, rfl⟩, hl⟩
      · subst h; obtain ⟨i, _, hi⟩ := mem_cstar.1 hl; simp [lit, nlit] at hi
      · have := (lit_mem_Bc hj).1 hl; subst this; exact mem_blocks.2 ⟨m, hm, rfl⟩
    · intro hC
      obtain ⟨m, hm, rfl⟩ := mem_blocks.1 hC
      exact ⟨Or.inr ⟨j, ⟨le_rfl, hj⟩, m, hm, rfl⟩, mem_Bc.2 (Or.inl rfl)⟩
  have hYF : (st k j).YF (lit j) = {cstar k} := by
    ext C
    simp only [State.YF, st, mem_filter, mem_insert, mem_bU, mem_Ico, mem_singleton]
    constructor
    · rintro ⟨h | ⟨i, _, m, _, rfl⟩, hl⟩
      · exact h
      · exact absurd hl nlit_not_Bc
    · rintro rfl
      exact ⟨Or.inl rfl, mem_cstar.2 ⟨j, hj, rfl⟩⟩
  have hle : (st k j).weight ((st k j).YF (lit j)) ≤ (st k j).weight ((st k j).YT (lit j)) := by
    rw [hYF, hYT]; unfold State.weight
    rw [sum_singleton]
    have : ∀ C ∈ blocks k j, (st k j).w C = 1 / 2 ^ k := by
      intro C hC
      obtain ⟨m, _, rfl⟩ := mem_blocks.1 hC
      simp only [st, wj]
      rw [if_neg (Ne.symm (cstar_ne_Bc k j m (by omega))), card_Bc k j m hj]
    rw [sum_congr rfl this, sum_const, card_blocks k j hk hj, nsmul_eq_mul]
    simp only [st, wj, if_pos rfl]
    push_cast; rw [div_eq_mul_one_div]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro hh
    have := hh (cstar k) (by simp [st]) (nlit j) (mem_cstar.2 ⟨j, hj, rfl⟩)
    exact this (by simp [State.inLIT, st, nlit])
  · simp [State.inLIT, st, lit]
  · refine ⟨Bc k j 0, ?_, mem_Bc.2 (Or.inl rfl)⟩
    simp only [st, mem_insert, mem_bU, mem_Ico]
    exact Or.inr ⟨j, ⟨le_rfl, hj⟩, 0, by positivity, rfl⟩
  · rw [update_of_le _ _ hle, hYT, hYF]
    simp only [st, State.mk.injEq]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [range_add_one, biUnion_insert, union_comm]
    · symm; ext C
      simp only [mem_sdiff, mem_insert, mem_bU, mem_Ico, mem_blocks]
      constructor
      · rintro ⟨h | ⟨i, hi, m, hm, rfl⟩, hnot⟩
        · exact Or.inl h
        · right
          refine ⟨i, ⟨?_, hi.2⟩, m, hm, rfl⟩
          rcases Nat.lt_or_ge j i with h | h
          · exact h
          · exfalso; have : i = j := by omega
            subst this; exact hnot ⟨m, hm, rfl⟩
      · rintro (rfl | ⟨i, hi, m, hm, rfl⟩)
        · refine ⟨Or.inl rfl, ?_⟩
          rintro ⟨m, _, h⟩; exact cstar_ne_Bc k j m (by omega) h
        · refine ⟨Or.inr ⟨i, ⟨by omega, hi.2⟩, m, hm, rfl⟩, ?_⟩
          rintro ⟨m', _, h⟩
          have := (Bc_inj hk hi.2 hj h).1; omega
    · rw [range_add_one, image_insert]
    · rw [range_add_one]; rfl
    · funext C; unfold doubleOn wj
      by_cases h : C = cstar k
      · rw [if_pos (mem_singleton.2 h), if_pos h, if_pos h, pow_succ]; ring
      · rw [if_neg (fun h' => h (mem_singleton.1 h')), if_neg h, if_neg h]

lemma st_reach (k : ℕ) (hk : 2 ≤ k) : ∀ j ≤ k, Reachable (Sw k) (st k j) := by
  intro j
  induction j with
  | zero => intro _; rw [st_zero]; exact Relation.ReflTransGen.refl
  | succ j ih => intro hj; exact (ih (by omega)).tail ⟨_, st_step k j hk (by omega)⟩

lemma st_halts (k : ℕ) : Halts (st k k) := by
  intro C hC l hl
  simp only [st, Ico_self, biUnion_empty, insert_empty_eq, mem_singleton] at hC
  subst hC
  obtain ⟨i, hi, rfl⟩ := mem_cstar.1 hl
  simp [State.inLIT, st, nlit, hi]

lemma card_st_sub (k : ℕ) (hk : 2 ≤ k) : (st k k).SUB.card = 2 ^ k - 1 := by
  simp only [st]
  rw [card_biUnion (fun i hi j hj hij => blocks_disj k hk i j (mem_range.1 hi) (mem_range.1 hj) hij)]
  rw [sum_congr rfl (fun j hj => card_blocks k j hk (mem_range.1 hj)), Nat.geomSum_eq le_rfl]
  simp

lemma card_Sw (k : ℕ) (hk : 2 ≤ k) : (Sw k).card = 2 ^ k := by
  unfold Sw
  rw [card_insert_of_notMem]
  · have := card_st_sub k hk; simp only [st] at this; rw [this]
    have : 1 ≤ 2 ^ k := Nat.one_le_two_pow; omega
  · rw [mem_bU]; rintro ⟨j, _, m, _, h⟩; exact cstar_ne_Bc k j m (by omega) h

lemma Sw_InMS (k : ℕ) : Shared.InMS k (Sw k) := by
  intro C hC
  simp only [Sw, mem_insert, mem_bU, mem_range] at hC
  rcases hC with rfl | ⟨j, hj, m, _, rfl⟩
  · rw [card_cstar]
  · rw [card_Bc k j m hj]

lemma Sw_opt (k : ℕ) (hk : 2 ≤ k) : Shared.opt (Sw k) = 2 ^ k := by
  apply le_antisymm ((opt_le_card _).trans (card_Sw k hk).le)
  rw [← card_Sw k hk]
  apply card_le_opt
  refine ⟨⟨{l | (l.pos = true ∧ k ≤ l.var) ∨ (l.pos = false ∧ l.var < k)}, fun l hl hneg => ?_⟩,
    fun C hC => ?_⟩
  · simp only [Set.mem_setOf_eq, Literal.neg] at hl hneg
    rcases hl with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases hneg with ⟨h3, h4⟩ | ⟨h3, h4⟩ <;>
      simp_all <;> omega
  · simp only [Sw, mem_insert, mem_bU, mem_range] at hC
    rcases hC with rfl | ⟨j, hj, m, _, rfl⟩
    · exact ⟨nlit 0, mem_cstar.2 ⟨0, by omega, rfl⟩, Or.inr ⟨rfl, by simp [nlit]; omega⟩⟩
    · exact ⟨fr k j m 0, mem_Bc.2 (Or.inr ⟨0, by omega, rfl⟩), Or.inl ⟨rfl, by simp [fr]⟩⟩

theorem ratio_core :
    (∀ k : ℕ, 1 ≤ k → ∀ S : Finset Shared.Clause, Shared.InMS k S → ∀ X : Finset Shared.Clause,
      Choosable S X → (2 ^ k - 1) * Shared.opt S ≤ 2 ^ k * X.card) ∧
    (∀ k : ℕ, 2 ≤ k → ∃ S : Finset Shared.Clause, Shared.InMS k S ∧ ∃ X : Finset Shared.Clause,
      Choosable S X ∧ 0 < X.card ∧ (2 ^ k - 1) * Shared.opt S = 2 ^ k * X.card) := by
  refine ⟨fun k _ S hS X ⟨σ, hσ, hh, hX⟩ => ?_, fun k hk => ?_⟩
  · rw [← hX]
    exact (Nat.mul_le_mul_left _ (opt_le_card S)).trans (halt_sub_core k S hS σ hσ hh).2
  · refine ⟨Sw k, Sw_InMS k, (st k k).SUB, ⟨st k k, st_reach k hk k le_rfl, st_halts k, rfl⟩,
      ?_, ?_⟩
    · rw [card_st_sub k hk]
      have : 2 ≤ 2 ^ k := by
        calc 2 = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    · rw [card_st_sub k hk, Sw_opt k hk, mul_comm]

end JohnsonApprox.MaxSatWeighted

open JohnsonApprox JohnsonApprox.MaxSatWeighted

theorem solution :
    (∀ k : ℕ, 1 ≤ k → ∀ S : Finset Shared.Clause, Shared.InMS k S → ∀ X : Finset Shared.Clause, Choosable S X →
      (2 ^ k - 1) * Shared.opt S ≤ 2 ^ k * X.card) ∧
    (∀ k : ℕ, 2 ≤ k → ∃ S : Finset Shared.Clause, Shared.InMS k S ∧ ∃ X : Finset Shared.Clause, Choosable S X ∧
      0 < X.card ∧ (2 ^ k - 1) * Shared.opt S = 2 ^ k * X.card) := by
  exact ratio_core
