-- Prove2me | solution 1 for LubyMIS.MonteCarlo.lemmaA
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T08:07:02.433573+00:00
-- url     : https://prove2.me/submissions/a808647d-82bf-42f1-a342-571d191cefc3

import Mathlib
import Definitions.Def_LubyMIS_MonteCarlo_Basic

namespace LubyMIS.MonteCarlo

open Finset

section aux_lA_section
open Classical

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- `w` is the strict minimum of `π` on `W`. -/
def aux_lA_SM {N : ℕ} (π : V → Fin N) (w : V) (W : Finset V) : Prop :=
  ∀ k ∈ W, k ≠ w → π w < π k

lemma aux_lA_SM_move {N : ℕ} (π : V → Fin N) (w w' : V) (W : Finset V) (_hw : w ∈ W)
    (hw' : w' ∈ W) (h : aux_lA_SM π w W) : aux_lA_SM (π ∘ Equiv.swap w w') w' W := by
  intro k hk hkw
  simp only [Function.comp_apply, Equiv.swap_apply_right]
  by_cases hkw0 : k = w
  · rw [hkw0, Equiv.swap_apply_left]
    exact h w' hw' (fun e => hkw (hkw0.trans e.symm))
  · rw [Equiv.swap_apply_of_ne_of_ne hkw0 hkw]
    exact h k hk hkw0

lemma aux_lA_SM_fix {N : ℕ} (π : V → Fin N) (w a b : V) (W : Finset V) (ha : a ∈ W) (hb : b ∈ W)
    (haw : a ≠ w) (hbw : b ≠ w) (h : aux_lA_SM π w W) :
    aux_lA_SM (π ∘ Equiv.swap a b) w W := by
  intro k hk hkw
  simp only [Function.comp_apply]
  rw [Equiv.swap_apply_of_ne_of_ne haw.symm hbw.symm]
  apply h
  · rcases eq_or_ne k a with h1 | h1
    · rw [h1, Equiv.swap_apply_left]; exact hb
    · rcases eq_or_ne k b with h2 | h2
      · rw [h2, Equiv.swap_apply_right]; exact ha
      · rw [Equiv.swap_apply_of_ne_of_ne h1 h2]; exact hk
  · intro e
    apply hkw
    have := congrArg (Equiv.swap a b) e
    rwa [Equiv.swap_apply_self, Equiv.swap_apply_of_ne_of_ne haw.symm hbw.symm] at this

lemma aux_lA_swap_card {N : ℕ} (Q : (V → Fin N) → Prop) (W : Finset V) (w w' : V)
    (hw : w ∈ W) (hw' : w' ∈ W) (hQ : ∀ π, Q π → Q (π ∘ Equiv.swap w w')) :
    (univ.filter (fun π : V → Fin N => Q π ∧ aux_lA_SM π w W)).card =
    (univ.filter (fun π : V → Fin N => Q π ∧ aux_lA_SM π w' W)).card := by
  have hinv : ∀ π : V → Fin N, (π ∘ Equiv.swap w w') ∘ Equiv.swap w w' = π := by
    intro π; funext x; simp [Function.comp_apply, Equiv.swap_apply_self]
  apply Finset.card_bij' (fun π _ => π ∘ Equiv.swap w w') (fun π _ => π ∘ Equiv.swap w w')
  · intro π hπ
    simp only [mem_filter, mem_univ, true_and] at hπ ⊢
    exact ⟨hQ π hπ.1, aux_lA_SM_move π w w' W hw hw' hπ.2⟩
  · intro π hπ
    simp only [mem_filter, mem_univ, true_and] at hπ ⊢
    refine ⟨hQ π hπ.1, ?_⟩
    rw [Equiv.swap_comm]
    exact aux_lA_SM_move π w' w W hw' hw hπ.2
  · intro π _; exact hinv π
  · intro π _; exact hinv π

lemma aux_lA_biUnion_card {N : ℕ} (Q : (V → Fin N) → Prop) (W : Finset V) (w : V) (hw : w ∈ W)
    (hQ : ∀ a ∈ W, ∀ b ∈ W, ∀ π, Q π → Q (π ∘ Equiv.swap a b)) :
    W.card * (univ.filter (fun π : V → Fin N => Q π ∧ aux_lA_SM π w W)).card =
    (W.biUnion (fun w' => univ.filter (fun π : V → Fin N => Q π ∧ aux_lA_SM π w' W))).card := by
  rw [Finset.card_biUnion]
  · rw [Finset.sum_congr rfl
      (fun w' hw' => (aux_lA_swap_card Q W w w' hw hw' (hQ w hw w' hw')).symm)]
    rw [Finset.sum_const, smul_eq_mul]
  · intro x hx y hy hxy
    rw [Function.onFun, Finset.disjoint_left]
    intro π h1 h2
    simp only [mem_filter, mem_univ, true_and] at h1 h2
    exact lt_asymm (h1.2 y hy (Ne.symm hxy)) (h2.2 x hx hxy)

lemma aux_lA_sum_le {N : ℕ} (Q : (V → Fin N) → Prop) (W : Finset V) (w : V) (hw : w ∈ W)
    (hQ : ∀ a ∈ W, ∀ b ∈ W, ∀ π, Q π → Q (π ∘ Equiv.swap a b)) :
    W.card * (univ.filter (fun π : V → Fin N => Q π ∧ aux_lA_SM π w W)).card ≤
    (univ.filter (fun π : V → Fin N => Q π)).card := by
  rw [aux_lA_biUnion_card Q W w hw hQ]
  apply Finset.card_le_card
  intro π hπ
  simp only [mem_biUnion, mem_filter, mem_univ, true_and] at hπ ⊢
  obtain ⟨_, _, h, _⟩ := hπ
  exact h

lemma aux_lA_sum_ge {N : ℕ} (Q : (V → Fin N) → Prop) (W : Finset V) (w : V) (hw : w ∈ W)
    (hQ : ∀ a ∈ W, ∀ b ∈ W, ∀ π, Q π → Q (π ∘ Equiv.swap a b))
    (hinj : ∀ π, Q π → Function.Injective π) :
    (univ.filter (fun π : V → Fin N => Q π)).card ≤
    W.card * (univ.filter (fun π : V → Fin N => Q π ∧ aux_lA_SM π w W)).card := by
  rw [aux_lA_biUnion_card Q W w hw hQ]
  apply Finset.card_le_card
  intro π hπ
  simp only [mem_biUnion, mem_filter, mem_univ, true_and] at hπ ⊢
  obtain ⟨x, hx, hmin⟩ := Finset.exists_min_image W π ⟨w, hw⟩
  refine ⟨x, hx, hπ, ?_⟩
  intro k hk hkx
  exact lt_of_le_of_ne (hmin k hk) (fun e => hkx ((hinj π hπ) e).symm)

variable (H : SimpleGraph V) [DecidableRel H.Adj]

/-- `j` beats all its neighbours. -/
def aux_lA_E {N : ℕ} (π : V → Fin N) (j : V) : Prop := ∀ k, H.Adj j k → π j < π k

lemma aux_lA_E_iff {N : ℕ} (π : V → Fin N) (j : V) :
    aux_lA_E H π j ↔ aux_lA_SM π j (insert j (H.neighborFinset j)) := by
  constructor
  · intro h k hk hkj
    rw [mem_insert] at hk
    rcases hk with hk | hk
    · exact absurd hk hkj
    · exact h k ((H.mem_neighborFinset j k).1 hk)
  · intro h k hadj
    exact h k (mem_insert_of_mem ((H.mem_neighborFinset j k).2 hadj)) (H.ne_of_adj hadj).symm

lemma aux_lA_card_ins (j : V) : (insert j (H.neighborFinset j)).card = H.degree j + 1 := by
  rw [card_insert_of_notMem (H.notMem_neighborFinset_self j), H.card_neighborFinset_eq_degree]

lemma aux_lA_F1 (N : ℕ) (j : V) :
    (univ.filter (fun π : V → Fin N => Function.Injective π)).card ≤
    (H.degree j + 1) *
      (univ.filter (fun π : V → Fin N => Function.Injective π ∧ aux_lA_E H π j)).card := by
  have h := aux_lA_sum_ge (fun π : V → Fin N => Function.Injective π)
    (insert j (H.neighborFinset j)) j (mem_insert_self _ _)
    (fun a _ b _ π hπ => hπ.comp (Equiv.injective _)) (fun π h => h)
  rw [aux_lA_card_ins] at h
  have heq : (univ.filter (fun π : V → Fin N => Function.Injective π ∧ aux_lA_E H π j)) =
      (univ.filter (fun π : V → Fin N => Function.Injective π ∧
        aux_lA_SM π j (insert j (H.neighborFinset j)))) := by
    ext π; simp only [mem_filter, mem_univ, true_and, aux_lA_E_iff]
  rw [heq]; convert h

lemma aux_lA_L (N : ℕ) (j l : V) (hjl : j ≠ l) :
    (H.degree j + 1) * (H.degree l + 1) *
      (univ.filter (fun π : V → Fin N => Function.Injective π ∧ aux_lA_E H π j ∧
        aux_lA_E H π l ∧ π j < π l)).card ≤
    (univ.filter (fun π : V → Fin N => Function.Injective π)).card := by
  by_cases hadj : H.Adj j l
  · have : (univ.filter (fun π : V → Fin N => Function.Injective π ∧ aux_lA_E H π j ∧
        aux_lA_E H π l ∧ π j < π l)) = ∅ := by
      apply Finset.filter_false_of_mem
      intro π _ h
      exact lt_asymm (h.2.1 l hadj) (h.2.2.1 j hadj.symm)
    rw [this]; simp
  · set U := insert l (H.neighborFinset l) with hU
    set T := insert j (H.neighborFinset j ∪ U) with hT
    have hjU : j ∉ U := by
      rw [hU, mem_insert, not_or]
      exact ⟨hjl, fun h => hadj ((H.mem_neighborFinset l j).1 h).symm⟩
    have hUT : U ⊆ T := fun x hx => mem_insert_of_mem (mem_union_right _ hx)
    have hcardU : U.card = H.degree l + 1 := aux_lA_card_ins H l
    have hcardT : H.degree j + 1 ≤ T.card := by
      rw [← aux_lA_card_ins H j]
      apply card_le_card
      intro x hx
      rw [mem_insert] at hx ⊢
      rcases hx with hx | hx
      · exact Or.inl hx
      · exact Or.inr (mem_union_left _ hx)
    have h1 : (univ.filter (fun π : V → Fin N => Function.Injective π ∧ aux_lA_E H π j ∧
        aux_lA_E H π l ∧ π j < π l)) ⊆
        (univ.filter (fun π : V → Fin N => (Function.Injective π ∧ aux_lA_SM π j T) ∧
          aux_lA_SM π l U)) := by
      intro π hπ
      simp only [mem_filter, mem_univ, true_and] at hπ ⊢
      obtain ⟨hinj, hEj, hEl, hlt⟩ := hπ
      refine ⟨⟨hinj, ?_⟩, (aux_lA_E_iff H π l).1 hEl⟩
      intro k hk hkj
      rw [hT, mem_insert] at hk
      rcases hk with hk | hk
      · exact absurd hk hkj
      rcases mem_union.1 hk with hk | hk
      · exact hEj k ((H.mem_neighborFinset j k).1 hk)
      · rw [hU, mem_insert] at hk
        rcases hk with hk | hk
        · rw [hk]; exact hlt
        · exact lt_trans hlt (hEl k ((H.mem_neighborFinset l k).1 hk))
    have h2 := aux_lA_sum_le (fun π : V → Fin N => Function.Injective π ∧ aux_lA_SM π j T) U l
      (mem_insert_self _ _)
      (fun a ha b hb π hπ => ⟨hπ.1.comp (Equiv.injective _),
        aux_lA_SM_fix π j a b T (hUT ha) (hUT hb) (fun e => hjU (e ▸ ha))
          (fun e => hjU (e ▸ hb)) hπ.2⟩)
    have h3 := aux_lA_sum_le (fun π : V → Fin N => Function.Injective π) T j
      (mem_insert_self _ _) (fun a _ b _ π hπ => hπ.comp (Equiv.injective _))
    rw [hcardU] at h2
    calc (H.degree j + 1) * (H.degree l + 1) *
          (univ.filter (fun π : V → Fin N => Function.Injective π ∧ aux_lA_E H π j ∧
            aux_lA_E H π l ∧ π j < π l)).card
        ≤ (H.degree j + 1) * ((H.degree l + 1) *
          (univ.filter (fun π : V → Fin N => (Function.Injective π ∧ aux_lA_SM π j T) ∧
            aux_lA_SM π l U)).card) := by
          rw [← mul_assoc]; exact Nat.mul_le_mul_left _ (card_le_card h1)
      _ ≤ (H.degree j + 1) *
          (univ.filter (fun π : V → Fin N => Function.Injective π ∧ aux_lA_SM π j T)).card :=
          Nat.mul_le_mul_left _ (by convert h2)
      _ ≤ T.card *
          (univ.filter (fun π : V → Fin N => Function.Injective π ∧ aux_lA_SM π j T)).card :=
          Nat.mul_le_mul_right _ hcardT
      _ ≤ _ := by convert h3

lemma aux_lA_F2 (N : ℕ) (j l : V) (hjl : j ≠ l) :
    (H.degree j + 1) * (H.degree l + 1) *
      (univ.filter (fun π : V → Fin N => Function.Injective π ∧ aux_lA_E H π j ∧
        aux_lA_E H π l)).card ≤
    2 * (univ.filter (fun π : V → Fin N => Function.Injective π)).card := by
  have hA := aux_lA_L H N j l hjl
  have hB := aux_lA_L H N l j (Ne.symm hjl)
  have hsub : (univ.filter (fun π : V → Fin N => Function.Injective π ∧ aux_lA_E H π j ∧
        aux_lA_E H π l)) ⊆
      (univ.filter (fun π : V → Fin N => Function.Injective π ∧ aux_lA_E H π j ∧
        aux_lA_E H π l ∧ π j < π l)) ∪
      (univ.filter (fun π : V → Fin N => Function.Injective π ∧ aux_lA_E H π l ∧
        aux_lA_E H π j ∧ π l < π j)) := by
    intro π hπ
    simp only [mem_filter, mem_univ, true_and, mem_union] at hπ ⊢
    obtain ⟨hinj, hEj, hEl⟩ := hπ
    rcases lt_trichotomy (π j) (π l) with h | h | h
    · exact Or.inl ⟨hinj, hEj, hEl, h⟩
    · exact absurd (hinj h) hjl
    · exact Or.inr ⟨hinj, hEl, hEj, h⟩
  have hc := (card_le_card hsub).trans (card_union_le _ _)
  calc (H.degree j + 1) * (H.degree l + 1) *
        (univ.filter (fun π : V → Fin N => Function.Injective π ∧ aux_lA_E H π j ∧
          aux_lA_E H π l)).card
      ≤ (H.degree j + 1) * (H.degree l + 1) *
        ((univ.filter (fun π : V → Fin N => Function.Injective π ∧ aux_lA_E H π j ∧
          aux_lA_E H π l ∧ π j < π l)).card +
        (univ.filter (fun π : V → Fin N => Function.Injective π ∧ aux_lA_E H π l ∧
          aux_lA_E H π j ∧ π l < π j)).card) := Nat.mul_le_mul_left _ hc
    _ ≤ _ := by
        rw [mul_add]
        have : (H.degree j + 1) * (H.degree l + 1) = (H.degree l + 1) * (H.degree j + 1) :=
          mul_comm _ _
        rw [this] at hA ⊢
        omega

/-- number of injective priority vectors for which some vertex of `S` is selected. -/
noncomputable def aux_lA_A (N : ℕ) (S : Finset V) : ℕ :=
  (univ.filter (fun π : V → Fin N => Function.Injective π ∧ ∃ j ∈ S, aux_lA_E H π j)).card

lemma aux_lA_F3 (N : ℕ) (S : Finset V) (k : V) :
    aux_lA_A H N S +
      (univ.filter (fun π : V → Fin N => Function.Injective π ∧ aux_lA_E H π k)).card ≤
    aux_lA_A H N (insert k S) + ∑ j ∈ S,
      (univ.filter (fun π : V → Fin N => Function.Injective π ∧ aux_lA_E H π j ∧
        aux_lA_E H π k)).card := by
  unfold aux_lA_A
  set X := univ.filter (fun π : V → Fin N => Function.Injective π ∧ ∃ j ∈ S, aux_lA_E H π j)
  set Y := univ.filter (fun π : V → Fin N => Function.Injective π ∧ aux_lA_E H π k)
  have hXY : univ.filter (fun π : V → Fin N => Function.Injective π ∧
      ∃ j ∈ insert k S, aux_lA_E H π j) = X ∪ Y := by
    ext π
    simp only [X, Y, mem_filter, mem_univ, true_and, mem_union, mem_insert, exists_eq_or_imp]
    constructor
    · rintro ⟨h1, h2 | h2⟩
      · exact Or.inr ⟨h1, h2⟩
      · exact Or.inl ⟨h1, h2⟩
    · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
      · exact ⟨h1, Or.inr h2⟩
      · exact ⟨h1, Or.inl h2⟩
  have hinter : (X ∩ Y).card ≤ ∑ j ∈ S,
      (univ.filter (fun π : V → Fin N => Function.Injective π ∧ aux_lA_E H π j ∧
        aux_lA_E H π k)).card := by
    refine le_trans (card_le_card ?_) card_biUnion_le
    intro π hπ
    simp only [X, Y, mem_inter, mem_filter, mem_univ, true_and, mem_biUnion] at hπ ⊢
    obtain ⟨⟨hinj, j, hj, hE⟩, _, hEk⟩ := hπ
    exact ⟨j, hj, hinj, hE, hEk⟩
  rw [hXY]
  have := card_union_add_card_inter X Y
  omega

lemma aux_lA_mono (N : ℕ) (S : Finset V) (k : V) :
    aux_lA_A H N S ≤ aux_lA_A H N (insert k S) := by
  unfold aux_lA_A
  apply card_le_card
  intro π hπ
  simp only [mem_filter, mem_univ, true_and] at hπ ⊢
  obtain ⟨hinj, j, hj, hE⟩ := hπ
  exact ⟨hinj, j, mem_insert_of_mem hj, hE⟩

lemma aux_lA_main (N : ℕ) (S : Finset V) :
    ((univ.filter (fun π : V → Fin N => Function.Injective π)).card : ℝ) *
      (min (∑ j ∈ S, 1 / ((H.degree j : ℝ) + 1)) (1 / 2) -
        (min (∑ j ∈ S, 1 / ((H.degree j : ℝ) + 1)) (1 / 2)) ^ 2) ≤
    (aux_lA_A H N S : ℝ) := by
  set K := ((univ.filter (fun π : V → Fin N => Function.Injective π)).card : ℝ) with hKdef
  have hK : 0 ≤ K := Nat.cast_nonneg _
  induction S using Finset.induction_on with
  | empty =>
    simp only [sum_empty]
    have : min (0:ℝ) (1/2) = 0 := min_eq_left (by norm_num)
    rw [this]; simp
  | @insert k S hkS ih =>
    rw [sum_insert hkS]
    set q0 := ∑ j ∈ S, 1 / ((H.degree j : ℝ) + 1) with hq0
    set p := 1 / ((H.degree k : ℝ) + 1) with hp
    have hdk : (0:ℝ) < (H.degree k : ℝ) + 1 := by positivity
    have hp0 : 0 < p := by positivity
    have hq00 : 0 ≤ q0 := sum_nonneg (fun j _ => by positivity)
    -- F3 in ℝ
    have h3 := aux_lA_F3 H N S k
    have h3r : (aux_lA_A H N S : ℝ) +
        ((univ.filter (fun π : V → Fin N => Function.Injective π ∧ aux_lA_E H π k)).card : ℝ) ≤
        (aux_lA_A H N (insert k S) : ℝ) + ∑ j ∈ S,
          ((univ.filter (fun π : V → Fin N => Function.Injective π ∧ aux_lA_E H π j ∧
            aux_lA_E H π k)).card : ℝ) := by
      exact_mod_cast h3
    -- F1 in ℝ
    have h1 := aux_lA_F1 H N k
    have h1r : K * p ≤
        ((univ.filter (fun π : V → Fin N => Function.Injective π ∧ aux_lA_E H π k)).card : ℝ) := by
      have : K ≤ ((H.degree k : ℝ) + 1) *
          ((univ.filter (fun π : V → Fin N => Function.Injective π ∧
            aux_lA_E H π k)).card : ℝ) := by
        rw [hKdef]; exact_mod_cast h1
      rw [hp, mul_one_div, div_le_iff₀ hdk]; linarith
    -- F2 in ℝ
    have h2r : ∑ j ∈ S,
          ((univ.filter (fun π : V → Fin N => Function.Injective π ∧ aux_lA_E H π j ∧
            aux_lA_E H π k)).card : ℝ) ≤ 2 * K * p * q0 := by
      rw [hq0, mul_sum]
      apply sum_le_sum
      intro j hj
      have hjk : j ≠ k := fun e => hkS (e ▸ hj)
      have h2 := aux_lA_F2 H N j k hjk
      have hdj : (0:ℝ) < (H.degree j : ℝ) + 1 := by positivity
      have h2' : ((H.degree j : ℝ) + 1) * ((H.degree k : ℝ) + 1) *
          ((univ.filter (fun π : V → Fin N => Function.Injective π ∧ aux_lA_E H π j ∧
            aux_lA_E H π k)).card : ℝ) ≤ 2 * K := by
        rw [hKdef]; exact_mod_cast h2
      rw [hp, show 2 * K * (1 / ((H.degree k : ℝ) + 1)) * (1 / ((H.degree j : ℝ) + 1)) =
        2 * K / (((H.degree j : ℝ) + 1) * ((H.degree k : ℝ) + 1)) by field_simp]
      rw [le_div_iff₀ (by positivity)]
      linarith
    have hmono : (aux_lA_A H N S : ℝ) ≤ (aux_lA_A H N (insert k S) : ℝ) := by
      exact_mod_cast aux_lA_mono H N S k
    by_cases hq : 1 / 2 ≤ q0
    · rw [min_eq_right hq] at ih
      rw [min_eq_right (by linarith : (1:ℝ) / 2 ≤ p + q0)]
      linarith
    · push Not at hq
      rw [min_eq_left hq.le] at ih
      have hbig : K * (q0 - q0 ^ 2) + K * p - 2 * K * p * q0 ≤
          (aux_lA_A H N (insert k S) : ℝ) := by linarith
      by_cases hq' : q0 + p ≤ 1 / 2
      · rw [min_eq_left (by linarith : p + q0 ≤ 1 / 2)]
        nlinarith [mul_nonneg hK (sq_nonneg p)]
      · push Not at hq'
        rw [min_eq_right (by linarith : (1:ℝ) / 2 ≤ p + q0)]
        have key : 1 / 4 ≤ q0 - q0 ^ 2 + p * (1 - 2 * q0) := by
          nlinarith [sq_nonneg (q0 - 1 / 2),
            mul_nonneg (by linarith : (0:ℝ) ≤ p - (1 / 2 - q0)) (by linarith : (0:ℝ) ≤ 1 - 2 * q0)]
        have := mul_le_mul_of_nonneg_left key hK
        nlinarith

lemma aux_lA_K (N : ℕ) :
    (univ.filter (fun π : V → Fin N => Function.Injective π)).card =
      N.descFactorial (Fintype.card V) := by
  rw [← Fintype.card_subtype]
  rw [Fintype.card_congr (Equiv.subtypeInjectiveEquivEmbedding V (Fin N))]
  rw [Fintype.card_embedding_eq, Fintype.card_fin]

end aux_lA_section

lemma aux_lA_desc (N : ℕ) : ∀ m : ℕ, m ≤ N →
    (N : ℝ) ^ m * ((N : ℝ) - (m : ℝ) * ((m : ℝ) - 1) / 2) ≤ (N.descFactorial m : ℝ) * N
  | 0, _ => by simp
  | m + 1, h => by
    have ih := aux_lA_desc N m (by omega)
    rw [Nat.descFactorial_succ]
    push_cast [Nat.cast_sub (by omega : m ≤ N)]
    have hNm : (0:ℝ) ≤ (N:ℝ) - m := by
      have : (m:ℝ) + 1 ≤ N := by exact_mod_cast h
      linarith
    have hpow : (0:ℝ) ≤ (N:ℝ) ^ m := by positivity
    have hm : (0:ℝ) ≤ (m:ℝ) := Nat.cast_nonneg m
    have hmm : (0:ℝ) ≤ (m:ℝ) * ((m:ℝ) - 1) := by
      rcases Nat.eq_zero_or_pos m with h0 | h0
      · simp [h0]
      · have : (1:ℝ) ≤ m := by exact_mod_cast h0
        nlinarith
    rw [pow_succ]
    nlinarith [mul_le_mul_of_nonneg_left ih hNm, mul_nonneg hpow (mul_nonneg hm hmm)]

end LubyMIS.MonteCarlo

open LubyMIS.MonteCarlo

theorem solution {V : Type*} [Fintype V] [DecidableEq V] (n : ℕ) (hn : 1 ≤ n)
    (hV : Fintype.card V ≤ n) (H : SimpleGraph V) [DecidableRel H.Adj] (i : V)
    (hi : 1 ≤ H.degree i) :
    probA n (fun π => i ∈ nbhd H (selectA H π)) ≥
      (1 / 4 * min (sumInv H i) 1) * (1 - 1 / (2 * (n : ℝ) ^ 2)) := by
  classical
  set N := n ^ 4 with hN
  set m := Fintype.card V with hm
  have hnr : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hNr : ((N : ℕ) : ℝ) = (n : ℝ) ^ 4 := by rw [hN]; push_cast; ring
  -- the injective count
  set K := (Finset.univ.filter (fun π : V → Fin N => Function.Injective π)).card with hKdef
  have hKd : (K : ℝ) = (N.descFactorial m : ℝ) := by
    rw [hKdef, aux_lA_K N]
  have hmN : m ≤ N := by
    rw [hN]
    calc m ≤ n := hV
      _ ≤ n ^ 4 := Nat.le_self_pow (by norm_num) n
  have hdesc := aux_lA_desc N m hmN
  have hKbound : ((n:ℝ) ^ 4) ^ m * (1 - 1 / (2 * (n:ℝ) ^ 2)) ≤ (K : ℝ) := by
    rw [hKd]
    rw [hNr] at hdesc
    have hn4 : (0:ℝ) < (n:ℝ) ^ 4 := by positivity
    have hmr : (m:ℝ) ≤ n := by exact_mod_cast hV
    have hm0 : (0:ℝ) ≤ m := Nat.cast_nonneg m
    have hmm : (m:ℝ) * ((m:ℝ) - 1) ≤ (n:ℝ) ^ 2 := by nlinarith
    have hpow : (0:ℝ) ≤ ((n:ℝ) ^ 4) ^ m := by positivity
    refine le_of_mul_le_mul_right ?_ hn4
    calc ((n:ℝ) ^ 4) ^ m * (1 - 1 / (2 * (n:ℝ) ^ 2)) * (n:ℝ) ^ 4
        = ((n:ℝ) ^ 4) ^ m * ((n:ℝ) ^ 4 - (n:ℝ) ^ 2 / 2) := by
          field_simp
      _ ≤ ((n:ℝ) ^ 4) ^ m * ((n:ℝ) ^ 4 - (m:ℝ) * ((m:ℝ) - 1) / 2) := by
          apply mul_le_mul_of_nonneg_left _ hpow
          linarith
      _ ≤ _ := hdesc
  -- main bound
  have hmain := aux_lA_main H N (H.neighborFinset i)
  rw [← hKdef] at hmain
  set q := ∑ j ∈ H.neighborFinset i, 1 / ((H.degree j : ℝ) + 1) with hq
  set s := sumInv H i with hs
  have hqs : s / 2 ≤ q := by
    rw [hs, sumInv, hq, Finset.sum_div]
    apply Finset.sum_le_sum
    intro j hj
    have hadj : H.Adj i j := (H.mem_neighborFinset i j).1 hj
    have hdj : 1 ≤ H.degree j := by
      rw [← H.card_neighborFinset_eq_degree]
      exact Finset.card_pos.mpr ⟨i, (H.mem_neighborFinset j i).2 hadj.symm⟩
    have hdjr : (1:ℝ) ≤ H.degree j := by exact_mod_cast hdj
    rw [div_div, div_le_div_iff₀ (by positivity) (by positivity)]
    linarith
  have hs0 : 0 ≤ s := by
    rw [hs, sumInv]
    exact Finset.sum_nonneg (fun j _ => by positivity)
  set μ := min q (1 / 2) with hμ
  have hμ1 : μ ≤ 1 / 2 := min_le_right _ _
  have hμ2 : min s 1 / 2 ≤ μ := by
    apply le_min
    · have := min_le_left s 1; linarith
    · have := min_le_right s 1; linarith
  have hmin0 : 0 ≤ min s 1 := le_min hs0 zero_le_one
  have hμμ : min s 1 / 4 ≤ μ - μ ^ 2 := by nlinarith
  have hK0 : (0:ℝ) ≤ K := Nat.cast_nonneg _
  have hA : (K:ℝ) * (min s 1 / 4) ≤ (aux_lA_A H N (H.neighborFinset i) : ℝ) :=
    le_trans (mul_le_mul_of_nonneg_left hμμ hK0) hmain
  -- event count
  have hEv : (aux_lA_A H N (H.neighborFinset i) : ℝ) ≤
      ((Finset.univ.filter (fun π₀ : V → Fin (n ^ 4) =>
        i ∈ nbhd H (selectA H (prioA π₀)))).card : ℝ) := by
    apply Nat.cast_le.mpr
    unfold aux_lA_A
    apply Finset.card_le_card
    intro π hπ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hπ ⊢
    obtain ⟨_, j, hj, hE⟩ := hπ
    unfold nbhd selectA
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨j, ?_, (H.mem_neighborFinset i j).1 hj⟩
    intro k hk
    have := hE k hk
    unfold prioA
    rw [Fin.lt_def] at this
    omega
  unfold probA
  rw [ge_iff_le, le_div_iff₀ (by positivity)]
  have hfin : (1 / 4 * min s 1) * (1 - 1 / (2 * (n : ℝ) ^ 2)) * ((n : ℝ) ^ 4) ^ m ≤
      ((Finset.univ.filter (fun π₀ : V → Fin (n ^ 4) =>
        i ∈ nbhd H (selectA H (prioA π₀)))).card : ℝ) := by
    have h1 : ((n:ℝ) ^ 4) ^ m * (1 - 1 / (2 * (n:ℝ) ^ 2)) * (min s 1 / 4) ≤
        (K : ℝ) * (min s 1 / 4) := mul_le_mul_of_nonneg_right hKbound (by positivity)
    calc (1 / 4 * min s 1) * (1 - 1 / (2 * (n : ℝ) ^ 2)) * ((n : ℝ) ^ 4) ^ m
        = ((n:ℝ) ^ 4) ^ m * (1 - 1 / (2 * (n:ℝ) ^ 2)) * (min s 1 / 4) := by ring
      _ ≤ _ := h1
      _ ≤ _ := hA
      _ ≤ _ := hEv
  refine le_trans hfin (le_of_eq ?_)
  congr 2
  ext π
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
