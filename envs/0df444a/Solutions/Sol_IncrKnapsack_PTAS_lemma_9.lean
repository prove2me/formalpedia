-- Prove2me | solution 1 for IncrKnapsack.PTAS.lemma_9
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T03:19:31.451877+00:00
-- url     : https://prove2.me/submissions/b9a51d5a-801d-4393-bff1-f95ed1a45f95

import Mathlib
import Definitions.Def_IncrKnapsack_PTAS_Model
import Theorems.Thm_IncrKnapsack_PTAS_representation_1

open Classical
open Finset BigOperators
open IncrKnapsack.PTAS

theorem ikp3_lamPlus_anti (I : Instance) (hI : I.Standing) (s t : Fin I.T) (h : s ≤ t) :
    lamPlus I t ≤ lamPlus I s := by
  unfold lamPlus
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro τ hτ; simp only [mem_filter, mem_univ, true_and] at hτ ⊢; exact le_trans h hτ
  · intro τ _ _; exact hI.lam_nonneg τ

theorem ikp3_lamPlus_pos (I : Instance) (hI : I.Standing) (t : Fin I.T) : 0 < lamPlus I t := by
  have tl_le : t ≤ (⟨I.T - 1, by have := hI.T_pos; omega⟩ : Fin I.T) := by
    rw [Fin.le_def]; simp; have := t.2; omega
  have := ikp3_lamPlus_anti I hI t _ tl_le
  have h2 : lamLast I ≤ lamPlus I ⟨I.T - 1, by have := hI.T_pos; omega⟩ := by
    unfold lamLast lamPlus; rw [dif_pos hI.T_pos]
    exact Finset.single_le_sum (f := I.lam) (fun τ _ => hI.lam_nonneg τ) (by simp)
  linarith [hI.lam_last_pos]

theorem ikp3_ivl_ex (I : Instance) (hI : I.Standing) (K : ℕ) (hK : 4 < K) (t : Fin I.T) :
    ∃ k : ℕ, (eps K / (I.n : ℝ)) ^ (k + 1) * lamTotal I < lamPlus I t := by
  have ht := ikp3_lamPlus_pos I hI t
  have hKpos : (0 : ℝ) < K := by exact_mod_cast (by omega : 0 < K)
  have hn : (1 : ℝ) ≤ I.n := by exact_mod_cast hI.n_pos
  have hr0 : 0 < eps K / (I.n : ℝ) := by unfold eps; positivity
  have hr1 : eps K / (I.n : ℝ) < 1 := by
    rw [div_lt_one (by linarith)]; unfold eps
    rw [div_lt_iff₀ hKpos]
    have : (5 : ℝ) ≤ K := by exact_mod_cast (by omega : 5 ≤ K)
    nlinarith
  have hLT : 0 < lamTotal I := by
    have hl : lamLast I ≤ lamTotal I := by
      unfold lamLast lamTotal; rw [dif_pos hI.T_pos]
      exact Finset.single_le_sum (fun t _ => hI.lam_nonneg t) (mem_univ _)
    linarith [hI.lam_last_pos]
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one (div_pos ht hLT) hr1
  refine ⟨k, ?_⟩
  have : (eps K / (I.n : ℝ)) ^ (k + 1) ≤ (eps K / (I.n : ℝ)) ^ k :=
    pow_le_pow_of_le_one hr0.le hr1.le (by omega)
  rw [lt_div_iff₀ hLT] at hk
  nlinarith

theorem ikp3_clus_mono (I : Instance) (hI : I.Standing) (K : ℕ) (hK : 4 < K) (ξ : ℕ)
    (s t : Fin I.T) (h : s ≤ t) : clus I K ξ s ≤ clus I K ξ t := by
  have hs := ikp3_ivl_ex I hI K hK s
  have ht := ikp3_ivl_ex I hI K hK t
  have hiv : ivl I K s ≤ ivl I K t := by
    unfold ivl; rw [dif_pos hs, dif_pos ht]
    apply Nat.find_min' hs
    exact lt_of_lt_of_le (Nat.find_spec ht) (ikp3_lamPlus_anti I hI s t h)
  unfold clus
  have : ((Finset.Ico 1 (ivl I K s + 1)).filter (fun m => m % K = ξ)) ⊆
      ((Finset.Ico 1 (ivl I K t + 1)).filter (fun m => m % K = ξ)) := by
    intro m hm; simp only [mem_filter, mem_Ico] at hm ⊢; omega
  have := Finset.card_le_card this
  omega

theorem ikp3_Ftil_nonneg (I : Instance) (hI : I.Standing) (K ξ : ℕ) (Φ : Finset ℝ)
    (A : Subroutine I) : ∀ m j ϕ, 0 ≤ Ftil I K ξ Φ A m j ϕ := by
  intro m
  induction m with
  | zero => intro j ϕ; simp only [Ftil]; split_ifs <;> simp
  | succ m ih =>
    intro j ϕ
    cases j with
    | zero => simp only [Ftil]; split_ifs <;> simp
    | succ j =>
      simp only [Ftil]
      apply Finset.le_inf
      intro q _
      have h1 := ih q.1 q.2
      have h2 : 0 ≤ wOpt (A (m + 1) q.1 j (phiReq I K ξ ϕ q.2)
          ((Ftil I K ξ Φ A m q.1 q.2).untopD 0)) := by
        cases A (m + 1) q.1 j (phiReq I K ξ ϕ q.2) ((Ftil I K ξ Φ A m q.1 q.2).untopD 0) with
        | none => simp [wOpt]
        | some S =>
          simp only [wOpt]
          exact_mod_cast (Finset.sum_nonneg (fun i _ => (hI.w_pos i).le))
      exact add_nonneg h1 h2

theorem ikp3_weight_split (I : Instance) (K ξ : ℕ) (S : Sol I) (m : ℕ) :
    weight I S = weight I (lowPart I K ξ S m) + weight I (highPart I K ξ S m) := by
  unfold weight
  rw [Finset.sum_filter, Finset.sum_filter, Finset.sum_filter, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro i _
  obtain h0 | ⟨t, h0⟩ : S i = none ∨ ∃ t, S i = some t := by
    cases S i <;> simp
  · simp [lowPart, highPart, h0]
  · by_cases h : clus I K ξ t ≤ m
    · simp [lowPart, highPart, h0, Option.filter_some, h, show ¬ m < clus I K ξ t by omega]
    · simp [lowPart, highPart, h0, Option.filter_some, h, show m < clus I K ξ t by omega]

theorem ikp3_contrib_split (I : Instance) (K ξ : ℕ) (S : Sol I) (m : ℕ) :
    contrib I (pr I K) S = contrib I (pr I K) (lowPart I K ξ S m) +
      contrib I (pr I K) (highPart I K ξ S m) := by
  unfold contrib
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro i _
  unfold psiItem
  simp only [lowPart, highPart]
  obtain h0 | ⟨t, h0⟩ : S i = none ∨ ∃ t, S i = some t := by
    cases S i <;> simp
  · rw [h0]; simp
  · rw [h0]
    by_cases h : clus I K ξ t ≤ m
    · simp [Option.filter_some, h, show ¬ m < clus I K ξ t by omega]
    · simp [Option.filter_some, h, show m < clus I K ξ t by omega]


/-- glue two solutions -/
def ikpG_glue {I : Instance} (S1 S2 : Sol I) : Sol I :=
  fun i => if (S1 i).isSome then S1 i else S2 i

theorem ikpG_glue_spec (I : Instance) (hI : I.Standing) (K ξ : ℕ) (m j' j : ℕ) (ϕ1 ϕ2 ω : ℝ)
    (S1 S2 : Sol I) (h1 : MultiFeas I K ξ m j' ϕ1 S1) (h2 : SingleFeas I K ξ (m + 1) j' j ϕ2 ω S2)
    (hω : weight I S1 ≤ ω) (hj' : j' ≤ j + 1) :
    MultiFeas I K ξ (m + 1) (j + 1) (ϕ1 + ϕ2) (ikpG_glue S1 S2) ∧
      weight I (ikpG_glue S1 S2) = weight I S1 + weight I S2 := by
  obtain ⟨f1, u1, r1, p1⟩ := h1
  obtain ⟨⟨r2, c2⟩, p2⟩ := h2
  have hdisj : ∀ i t s, S1 i = some t → S2 i = some s → False := by
    intro i t s a b
    have := (r1 i t a).2.2; have := (r2 i s b).2.2.1; omega
  have hG : ∀ i t, ikpG_glue S1 S2 i = some t ↔ S1 i = some t ∨ S2 i = some t := by
    intro i t
    unfold ikpG_glue
    cases h : S1 i with
    | none => simp
    | some t1 =>
      simp only [Option.isSome_some, if_true]
      constructor
      · intro h'; exact Or.inl h'
      · rintro (h' | h')
        · exact h'
        · exact absurd (hdisj i t1 t h h') id
  have hsum : ∀ f : Fin I.n → ℝ, ∀ T1 T2 : Finset (Fin I.n),
      (∀ i, i ∈ T1 → i ∈ T2 → False) →
      ∑ i ∈ T1 ∪ T2, f i = ∑ i ∈ T1, f i + ∑ i ∈ T2, f i := by
    intro f T1 T2 hd
    exact Finset.sum_union (Finset.disjoint_left.2 (fun a b c => hd _ b c))
  have hsetG : ∀ t, Sol.set (ikpG_glue S1 S2) t = Sol.set S1 t ∪ Sol.set S2 t := by
    intro t; ext i
    simp only [Sol.set, mem_union, mem_filter, mem_univ, true_and, hG]
    constructor
    · rintro ⟨s, hs | hs, hst⟩
      · exact Or.inl ⟨s, hs, hst⟩
      · exact Or.inr ⟨s, hs, hst⟩
    · rintro (⟨s, hs, hst⟩ | ⟨s, hs, hst⟩)
      · exact ⟨s, Or.inl hs, hst⟩
      · exact ⟨s, Or.inr hs, hst⟩
  have hdset : ∀ t t', ∀ i, i ∈ Sol.set S1 t → i ∈ Sol.set S2 t' → False := by
    intro t t' i a b
    simp only [Sol.set, mem_filter, mem_univ, true_and] at a b
    obtain ⟨s, hs, _⟩ := a; obtain ⟨s', hs', _⟩ := b
    exact hdisj i s s' hs hs'
  have hweight : weight I (ikpG_glue S1 S2) = weight I S1 + weight I S2 := by
    unfold weight
    have : univ.filter (fun i => (ikpG_glue S1 S2 i).isSome) =
        univ.filter (fun i => (S1 i).isSome) ∪ univ.filter (fun i => (S2 i).isSome) := by
      ext i
      simp only [mem_union, mem_filter, mem_univ, true_and, Option.isSome_iff_exists, hG]
      constructor
      · rintro ⟨t, ht | ht⟩
        · exact Or.inl ⟨t, ht⟩
        · exact Or.inr ⟨t, ht⟩
      · rintro (⟨t, ht⟩ | ⟨t, ht⟩)
        · exact ⟨t, Or.inl ht⟩
        · exact ⟨t, Or.inr ht⟩
    rw [this]
    apply hsum
    intro i a b
    simp only [mem_filter, mem_univ, true_and, Option.isSome_iff_exists] at a b
    obtain ⟨t, ht⟩ := a; obtain ⟨s, hs⟩ := b
    exact hdisj i t s ht hs
  refine ⟨⟨?_, ⟨?_, ?_⟩, ?_, ?_⟩, hweight⟩
  · -- feasibility
    intro t
    rw [hsetG, hsum _ _ _ (hdset t t)]
    by_cases hne : (Sol.set S2 t).Nonempty
    · obtain ⟨i0, hi0⟩ := hne
      have hi0' := hi0
      simp only [Sol.set, mem_filter, mem_univ, true_and] at hi0'
      obtain ⟨s0, hs0, hs0t⟩ := hi0'
      obtain ⟨hg0, hc0, _⟩ := r2 i0 s0 hs0
      set C := univ.filter (fun s : Fin I.T => IsGood I K ξ s ∧ clus I K ξ s = m + 1 ∧ s ≤ t)
      have hCne : C.Nonempty := ⟨s0, by simp [C, hg0, hc0, hs0t]⟩
      set t' := C.max' hCne
      have ht'C : t' ∈ C := C.max'_mem hCne
      simp only [C, mem_filter, mem_univ, true_and] at ht'C
      obtain ⟨hgt', hct', ht't⟩ := ht'C
      have hsub : Sol.set S2 t ⊆ Sol.set S2 t' := by
        intro i hi
        simp only [Sol.set, mem_filter, mem_univ, true_and] at hi ⊢
        obtain ⟨s, hs, hst⟩ := hi
        obtain ⟨hg, hc, _⟩ := r2 i s hs
        exact ⟨s, hs, C.le_max' s (by simp [C, hg, hc, hst])⟩
      have hcap := c2 t' hgt' hct'
      have hpos : 0 < ∑ i ∈ Sol.set S2 t', I.w i :=
        Finset.sum_pos (fun i _ => hI.w_pos i) ⟨i0, hsub hi0⟩
      have hmax : ∑ i ∈ Sol.set S2 t', I.w i ≤ I.W t' - ω := by
        rcases le_or_gt (I.W t' - ω) 0 with h | h
        · rw [max_eq_right h] at hcap; linarith
        · rwa [max_eq_left h.le] at hcap
      have h2le : ∑ i ∈ Sol.set S2 t, I.w i ≤ ∑ i ∈ Sol.set S2 t', I.w i :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ => (hI.w_pos i).le)
      have h1le : ∑ i ∈ Sol.set S1 t, I.w i ≤ weight I S1 := by
        unfold weight
        apply Finset.sum_le_sum_of_subset_of_nonneg _ (fun i _ _ => (hI.w_pos i).le)
        intro i hi
        simp only [Sol.set, mem_filter, mem_univ, true_and] at hi ⊢
        obtain ⟨s, hs, _⟩ := hi; simp [hs]
      have := hI.W_mono ht't
      linarith
    · rw [Finset.not_nonempty_iff_eq_empty] at hne
      rw [hne, Finset.sum_empty, add_zero]; exact f1 t
  · -- uncrossing (1)
    intro i k t s hi hk hc
    rw [hG] at hi hk
    rcases hi with hi | hi <;> rcases hk with hk | hk
    · exact u1.1 i k t s hi hk hc
    · have := (r1 i t hi).2.2; have := (r2 k s hk).2.2.1; omega
    · have := (r2 i t hi).2.2.1; have := (r1 k s hk).2.2; omega
    · rw [(r2 i t hi).2.1, (r2 k s hk).2.1]
  · -- uncrossing (2)
    intro i k t s hi hk hc
    rw [hG] at hi hk
    rcases hi with hi | hi <;> rcases hk with hk | hk
    · exact u1.2 i k t s hi hk hc
    · have := (r1 i t hi).2.1; have := (r2 k s hk).2.1; omega
    · have := (r2 i t hi).2.2.1; have := (r1 k s hk).2.2; omega
    · rw [(r2 i t hi).2.1, (r2 k s hk).2.1]
  · intro i t h
    rw [hG] at h
    rcases h with h | h
    · obtain ⟨a, b, c⟩ := r1 i t h; exact ⟨a, by omega, by omega⟩
    · obtain ⟨a, b, _, c⟩ := r2 i t h; exact ⟨a, by omega, by omega⟩
  · -- profit
    have : contrib I (pr I K) (ikpG_glue S1 S2) = contrib I (pr I K) S1 + contrib I (pr I K) S2 := by
      unfold contrib; rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl; intro i _
      unfold psiItem
      cases h1' : S1 i with
      | none =>
        have : ikpG_glue S1 S2 i = S2 i := by simp [ikpG_glue, h1']
        rw [this]; simp
      | some t =>
        have : ikpG_glue S1 S2 i = some t := by simp [ikpG_glue, h1']
        rw [this]
        cases h2' : S2 i with
        | none => simp
        | some s => exact absurd (hdisj i t s h1' h2') id
    rw [this]; linarith

/-- Splitting an exact-DP solution at cluster `m`. -/
theorem ikpG_split (I : Instance) (hI : I.Standing) (K : ℕ) (hK : 4 < K) (ξ : ℕ) (m j : ℕ)
    (ϕ : ℝ) (S : Sol I) (hS : MultiFeas I K ξ (m + 1) (j + 1) ϕ S) (ω : ℝ)
    (hω : ω ≤ weight I (lowPart I K ξ S m)) :
    classTop I K (lowPart I K ξ S m) ≤ j + 1 ∧
    (∀ ϕ', ϕ' ≤ contrib I (pr I K) (lowPart I K ξ S m) →
      MultiFeas I K ξ m (classTop I K (lowPart I K ξ S m)) ϕ' (lowPart I K ξ S m)) ∧
    (∀ φ, φ ≤ contrib I (pr I K) (highPart I K ξ S m) →
      SingleFeas I K ξ (m + 1) (classTop I K (lowPart I K ξ S m)) j φ ω
        (highPart I K ξ S m)) := by
  obtain ⟨hSfeas, hSus, hSin, _⟩ := hS
  set Lo := lowPart I K ξ S m with hLo
  set Hi := highPart I K ξ S m with hHi
  have hLo_some : ∀ i t, Lo i = some t → S i = some t ∧ clus I K ξ t ≤ m := by
    intro i t h
    simp only [hLo, lowPart, Option.filter_eq_some_iff, decide_eq_true_eq] at h
    exact h
  have hHi_some : ∀ i t, Hi i = some t → S i = some t ∧ m < clus I K ξ t := by
    intro i t h
    simp only [hHi, highPart, Option.filter_eq_some_iff, decide_eq_true_eq] at h
    exact h
  set j' := classTop I K Lo with hj'
  refine ⟨?_, ?_, ?_⟩
  · rw [hj']; unfold classTop
    apply Finset.sup_le; intro i hi
    simp only [mem_filter, mem_univ, true_and] at hi
    obtain ⟨t, ht⟩ := Option.isSome_iff_exists.1 hi
    have := (hSin i t (hLo_some i t ht).1).2.2; omega
  · intro ϕ' hϕ'
    refine ⟨?_, ?_, ?_, hϕ'⟩
    · intro t
      refine le_trans ?_ (hSfeas t)
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro i hi
        simp only [Sol.set, mem_filter, mem_univ, true_and] at hi ⊢
        obtain ⟨s, hs, hst⟩ := hi
        exact ⟨s, (hLo_some i s hs).1, hst⟩
      · intro i _ _; exact (hI.w_pos i).le
    · constructor
      · intro i k t s hi hk hc
        exact hSus.1 i k t s (hLo_some i t hi).1 (hLo_some k s hk).1 hc
      · intro i k t s hi hk hc
        exact hSus.2 i k t s (hLo_some i t hi).1 (hLo_some k s hk).1 hc
    · intro i t h
      obtain ⟨h1, h2⟩ := hLo_some i t h
      refine ⟨(hSin i t h1).1, h2, ?_⟩
      have : cls I K i + 1 ≤ j' := by
        rw [hj']; unfold classTop
        exact Finset.le_sup (f := fun i => cls I K i + 1) (by simp [h])
      omega
  · intro φ hφ
    refine ⟨⟨?_, ?_⟩, hφ⟩
    · intro i t h
      obtain ⟨h1, h2⟩ := hHi_some i t h
      obtain ⟨hg, hc, hcl⟩ := hSin i t h1
      refine ⟨hg, by omega, ?_, by omega⟩
      rw [hj']; unfold classTop
      apply Finset.sup_le; intro k hk
      simp only [mem_filter, mem_univ, true_and] at hk
      obtain ⟨s, hs⟩ := Option.isSome_iff_exists.1 hk
      obtain ⟨hk1, hk2⟩ := hLo_some k s hs
      by_contra hlt
      push_neg at hlt
      rcases Nat.lt_or_ge (cls I K i) (cls I K k) with h3 | h3
      · have := hSus.2 i k t s h1 hk1 h3; omega
      · have h4 : cls I K i = cls I K k := by omega
        have := hSus.1 i k t s h1 hk1 h4; omega
    · intro t hg hc
      have hsub : Sol.set Hi t ∪ univ.filter (fun i => (Lo i).isSome) ⊆ Sol.set S t := by
        intro i hi
        rw [mem_union] at hi
        simp only [Sol.set, mem_filter, mem_univ, true_and] at hi ⊢
        rcases hi with ⟨s, hs, hst⟩ | hi
        · exact ⟨s, (hHi_some i s hs).1, hst⟩
        · obtain ⟨s, hs⟩ := Option.isSome_iff_exists.1 hi
          obtain ⟨hs1, hs2⟩ := hLo_some i s hs
          refine ⟨s, hs1, ?_⟩
          by_contra hst; push_neg at hst
          have := ikp3_clus_mono I hI K hK ξ t s hst.le; omega
      have hdisj : Disjoint (Sol.set Hi t) (univ.filter (fun i => (Lo i).isSome)) := by
        rw [Finset.disjoint_left]
        intro i hi hi'
        simp only [Sol.set, mem_filter, mem_univ, true_and] at hi hi'
        obtain ⟨s, hs, _⟩ := hi
        obtain ⟨s', hs'⟩ := Option.isSome_iff_exists.1 hi'
        have a1 := hHi_some i s hs
        have a2 := hLo_some i s' hs'
        rw [a1.1] at a2; cases a2.1; omega
      have h1 := Finset.sum_le_sum_of_subset_of_nonneg hsub
        (f := I.w) (fun i _ _ => (hI.w_pos i).le)
      rw [Finset.sum_union hdisj] at h1
      have h2 := hSfeas t
      have : ∑ i ∈ Sol.set Hi t, I.w i ≤ I.W t - ω := by
        unfold weight at hω; linarith
      exact le_trans this (le_max_left _ _)

theorem ikpG_F_le (I : Instance) (K ξ m j : ℕ) (ϕ : ℝ) (S : Sol I)
    (h : MultiFeas I K ξ m j ϕ S) : F I K ξ m j ϕ ≤ ((weight I S : ℝ) : WithTop ℝ) := by
  unfold F; exact Finset.inf_le (by simp [h])

theorem ikpG_OPT_le (I : Instance) (K ξ m a b : ℕ) (φ ω : ℝ) (S : Sol I)
    (h : SingleFeas I K ξ m a b φ ω S) : OPTsingle I K ξ m a b φ ω ≤ ((weight I S : ℝ) : WithTop ℝ) := by
  unfold OPTsingle; exact Finset.inf_le (by simp [h])

theorem ikpG_F_attain (I : Instance) (K ξ m j : ℕ) (ϕ : ℝ) (h : F I K ξ m j ϕ < ⊤) :
    ∃ S, MultiFeas I K ξ m j ϕ S ∧ F I K ξ m j ϕ = ((weight I S : ℝ) : WithTop ℝ) := by
  unfold F at h ⊢
  have hne : (univ.filter (MultiFeas I K ξ m j ϕ)).Nonempty := by
    by_contra hne
    rw [Finset.not_nonempty_iff_eq_empty] at hne
    rw [hne, Finset.inf_empty] at h; exact lt_irrefl _ h
  obtain ⟨S, hS, hmin⟩ := Finset.exists_min_image _ (fun S => weight I S) hne
  refine ⟨S, by simpa using hS, le_antisymm (Finset.inf_le hS) (Finset.le_inf ?_)⟩
  intro S' hS'; exact_mod_cast hmin S' hS'

theorem ikpG_OPT_attain (I : Instance) (K ξ m a b : ℕ) (φ ω : ℝ)
    (h : OPTsingle I K ξ m a b φ ω < ⊤) :
    ∃ S, SingleFeas I K ξ m a b φ ω S ∧
      OPTsingle I K ξ m a b φ ω = ((weight I S : ℝ) : WithTop ℝ) := by
  unfold OPTsingle at h ⊢
  have hne : (univ.filter (SingleFeas I K ξ m a b φ ω)).Nonempty := by
    by_contra hne
    rw [Finset.not_nonempty_iff_eq_empty] at hne
    rw [hne, Finset.inf_empty] at h; exact lt_irrefl _ h
  obtain ⟨S, hS, hmin⟩ := Finset.exists_min_image _ (fun S => weight I S) hne
  refine ⟨S, by simpa using hS, le_antisymm (Finset.inf_le hS) (Finset.le_inf ?_)⟩
  intro S' hS'; exact_mod_cast hmin S' hS'

theorem solution (I : Instance) (hI : I.Standing) (K : ℕ) (hK : 4 < K) (ξ : ℕ) (hξ : ξ < K)
    (m j : ℕ) (ϕ : ℝ) (S : Sol I) (hS : MultiFeas I K ξ (m + 1) (j + 1) ϕ S)
    (hSopt : ((weight I S : ℝ) : WithTop ℝ) = F I K ξ (m + 1) (j + 1) ϕ) :
    F I K ξ m (classTop I K (lowPart I K ξ S m)) (contrib I (pr I K) (lowPart I K ξ S m)) =
        ((weight I (lowPart I K ξ S m) : ℝ) : WithTop ℝ) ∧
      OPTsingle I K ξ (m + 1) (classTop I K (lowPart I K ξ S m)) j
          (ϕ - contrib I (pr I K) (lowPart I K ξ S m)) (weight I (lowPart I K ξ S m)) =
        ((weight I (highPart I K ξ S m) : ℝ) : WithTop ℝ) := by
  set Lo := lowPart I K ξ S m with hLo
  set Hi := highPart I K ξ S m with hHi
  set j' := classTop I K Lo with hj'
  set ϕL := contrib I (pr I K) Lo with hϕL
  have hcs := ikp3_contrib_split I K ξ S m
  have hws := ikp3_weight_split I K ξ S m
  rw [← hLo, ← hHi, ← hϕL] at hcs
  rw [← hLo, ← hHi] at hws
  have hprof := hS.2.2.2
  obtain ⟨hj'le, hLoF, hHiF⟩ := ikpG_split I hI K hK ξ m j ϕ S hS (weight I Lo) le_rfl
  have hHi1 : SingleFeas I K ξ (m + 1) j' j (ϕ - ϕL) (weight I Lo) Hi :=
    hHiF _ (by linarith)
  have hLo1 : MultiFeas I K ξ m j' ϕL Lo := hLoF ϕL le_rfl
  have hFS : ∀ G, MultiFeas I K ξ (m + 1) (j + 1) ϕ G → weight I S ≤ weight I G := by
    intro G hG
    have := ikpG_F_le I K ξ (m + 1) (j + 1) ϕ G hG
    rw [← hSopt] at this; exact_mod_cast this
  constructor
  · apply le_antisymm (ikpG_F_le I K ξ m j' ϕL Lo hLo1)
    unfold F
    apply Finset.le_inf
    intro L' hL'
    simp only [mem_filter, mem_univ, true_and] at hL'
    by_contra hlt
    push_neg at hlt
    have hlt' : weight I L' < weight I Lo := by exact_mod_cast hlt
    obtain ⟨hG, hwG⟩ := ikpG_glue_spec I hI K ξ m j' j ϕL (ϕ - ϕL) (weight I Lo) L' Hi hL' hHi1
      hlt'.le hj'le
    rw [show ϕL + (ϕ - ϕL) = ϕ by ring] at hG
    have := hFS _ hG
    linarith
  · apply le_antisymm (ikpG_OPT_le I K ξ (m + 1) j' j (ϕ - ϕL) (weight I Lo) Hi hHi1)
    unfold OPTsingle
    apply Finset.le_inf
    intro H' hH'
    simp only [mem_filter, mem_univ, true_and] at hH'
    obtain ⟨hG, hwG⟩ := ikpG_glue_spec I hI K ξ m j' j ϕL (ϕ - ϕL) (weight I Lo) Lo H' hLo1 hH'
      le_rfl hj'le
    rw [show ϕL + (ϕ - ϕL) = ϕ by ring] at hG
    have := hFS _ hG
    have : weight I Hi ≤ weight I H' := by linarith
    exact_mod_cast this
