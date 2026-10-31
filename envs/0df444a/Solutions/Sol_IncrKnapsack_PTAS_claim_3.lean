-- Prove2me | solution 1 for IncrKnapsack.PTAS.claim_3
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T03:15:27.784153+00:00
-- url     : https://prove2.me/submissions/4b0931c8-52d0-4716-a3d2-3eca5c32a15c

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

theorem ikp3_empty_case (I : Instance) (hI : I.Standing) (K : ℕ) (S : Sol I) (ϕ : ℝ)
    (hϕ0 : 0 ≤ ϕ) (hnone : ∀ i, S i = none) (hϕ : ϕ ≤ contrib I (pr I K) S) :
    (if ϕ = 0 then (0 : WithTop ℝ) else ⊤) ≤ ((weight I S : ℝ) : WithTop ℝ) := by
  have hc : contrib I (pr I K) S = 0 := by
    unfold contrib; apply Finset.sum_eq_zero; intro i _; unfold psiItem; rw [hnone i]
  have : ϕ = 0 := by linarith
  rw [if_pos this]
  exact_mod_cast (Finset.sum_nonneg (fun i _ => (hI.w_pos i).le))

theorem solution (I : Instance) (hI : I.Standing) (K : ℕ) (hK : 4 < K) (ξ : ℕ) (hξ : ξ < K)
    (Φ : Finset ℝ) (A : Subroutine I)
    (hΦ : IsProfitGrid I K ξ Φ) (hA : IsSubroutine I K ξ A) :
    ∀ m : ℕ, m ≤ Mcl I K ξ → ∀ j : ℕ, j ≤ Lmax I K + 1 → ∀ ϕ ∈ Φ,
      Ftil I K ξ Φ A m j ϕ ≤ F I K ξ m j ϕ := by
  have hpr : ∀ i, 0 ≤ pr I K i := fun i => by unfold pr eps; positivity
  have hlam : ∀ t, 0 ≤ lamPlus I t := by
    intro t; unfold lamPlus; exact Finset.sum_nonneg (fun τ _ => hI.lam_nonneg τ)
  have hLT0 : 0 ≤ lamTotal I := by
    unfold lamTotal; exact Finset.sum_nonneg (fun τ _ => hI.lam_nonneg τ)
  have hcontrib_nn : ∀ S : Sol I, 0 ≤ contrib I (pr I K) S := by
    intro S; unfold contrib; apply Finset.sum_nonneg; intro i _; unfold psiItem
    split
    · exact mul_nonneg (hpr i) (hlam _)
    · exact le_refl _
  have hcontrib_le : ∀ S : Sol I, contrib I (pr I K) S ≤ lamTotal I * ∑ i, pr I K i := by
    intro S; unfold contrib; rw [Finset.mul_sum]
    apply Finset.sum_le_sum; intro i _; unfold psiItem
    split
    · rw [mul_comm]
      apply mul_le_mul_of_nonneg_right _ (hpr i)
      unfold lamPlus lamTotal
      exact Finset.sum_le_sum_of_subset_of_nonneg (subset_univ _)
        (fun τ _ _ => hI.lam_nonneg τ)
    · exact mul_nonneg hLT0 (hpr i)
  have hclus1 : ∀ t, 1 ≤ clus I K ξ t := by intro t; unfold clus; omega
  have key : ∀ m, m ≤ Mcl I K ξ → ∀ j ϕ, ϕ ∈ Φ → ∀ S, MultiFeas I K ξ m j ϕ S →
      Ftil I K ξ Φ A m j ϕ ≤ ((weight I S : ℝ) : WithTop ℝ) := by
    intro m
    induction m with
    | zero =>
      intro _ j ϕ hϕ S hS
      rw [show Ftil I K ξ Φ A 0 j ϕ = if ϕ = 0 then 0 else ⊤ by simp [Ftil]]
      apply ikp3_empty_case I hI K S ϕ (hΦ.2.1 ϕ hϕ) _ hS.2.2.2
      intro i
      by_contra h
      obtain ⟨t, ht⟩ := Option.ne_none_iff_exists'.1 h
      have := (hS.2.2.1 i t ht).2.1
      have := hclus1 t; omega
    | succ m ih =>
      intro hm j ϕ hϕ S hS
      obtain ⟨hSfeas, hSus, hSin, hSprof⟩ := hS
      cases j with
      | zero =>
        rw [show Ftil I K ξ Φ A (m + 1) 0 ϕ = if ϕ = 0 then 0 else ⊤ by simp [Ftil]]
        apply ikp3_empty_case I hI K S ϕ (hΦ.2.1 ϕ hϕ) _ hSprof
        intro i
        by_contra h
        obtain ⟨t, ht⟩ := Option.ne_none_iff_exists'.1 h
        have := (hSin i t ht).2.2; omega
      | succ j0 =>
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
        set ϕL := contrib I (pr I K) Lo with hϕL
        set ϕ1 := min ϕL ϕ with hϕ1
        have hϕ0 : 0 ≤ ϕ := hΦ.2.1 ϕ hϕ
        have hϕ1nn : 0 ≤ ϕ1 := le_min (hcontrib_nn Lo) hϕ0
        have hϕ1le : ϕ1 ≤ lamTotal I * ∑ i, pr I K i :=
          le_trans (min_le_left _ _) (hcontrib_le Lo)
        have hMpos : 0 < Mcl I K ξ := by omega
        obtain ⟨x, hxΦ, hxle, hxge⟩ := hΦ.2.2 hMpos ϕ1 hϕ1nn hϕ1le
        -- the low part is feasible for the smaller multi-cluster instance
        have hLo_feas : MultiFeas I K ξ m j' x Lo := by
          refine ⟨?_, ?_, ?_, ?_⟩
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
          · exact le_trans hxle (min_le_left _ _)
        have hIH := ih (by omega) j' x hxΦ Lo hLo_feas
        -- j' ≤ j0 + 1
        have hj'le : j' ≤ j0 + 1 := by
          rw [hj']; unfold classTop
          apply Finset.sup_le; intro i hi
          simp only [mem_filter, mem_univ, true_and] at hi
          obtain ⟨t, ht⟩ := Option.isSome_iff_exists.1 hi
          have := (hSin i t (hLo_some i t ht).1).2.2; omega
        -- ω
        set ω := (Ftil I K ξ Φ A m j' x).untopD 0 with hω
        have hFfin : Ftil I K ξ Φ A m j' x ≠ ⊤ :=
          ne_top_of_le_ne_top WithTop.coe_ne_top hIH
        have hFω : Ftil I K ξ Φ A m j' x = (ω : WithTop ℝ) := by
          obtain ⟨v, hv⟩ := WithTop.ne_top_iff_exists.1 hFfin
          rw [hω, ← hv]; rfl
        have hω0 : 0 ≤ ω := by
          have := ikp3_Ftil_nonneg I hI K ξ Φ A m j' x
          rw [hFω] at this; exact_mod_cast this
        have hωL : ω ≤ weight I Lo := by
          have := hIH; rw [hFω] at this; exact_mod_cast this
        -- φ
        set φ := phiReq I K ξ ϕ x with hφ
        have hφ0 : 0 ≤ φ := by rw [hφ]; unfold phiReq; exact le_max_right _ _
        -- the high part is feasible for the single-cluster instance
        have hHi_feas : SingleFeas I K ξ (m + 1) j' j0 φ ω Hi := by
          refine ⟨⟨?_, ?_⟩, ?_⟩
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
            -- earlier clusters lie strictly before t
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
              unfold weight at hωL; linarith
            exact le_trans this (le_max_left _ _)
          · -- profit
            have hsplit := ikp3_contrib_split I K ξ S m
            rw [← hLo, ← hHi, ← hϕL] at hsplit
            have hH0 := hcontrib_nn Hi
            have : φ ≤ max (ϕ - ϕ1) 0 := by
              rw [hφ]; unfold phiReq
              apply max_le_max _ le_rfl
              linarith
            refine le_trans this (max_le ?_ hH0)
            rcases le_total ϕL ϕ with h | h
            · rw [hϕ1, min_eq_left h]; linarith
            · rw [hϕ1, min_eq_right h]; linarith
        -- the subroutine call
        obtain ⟨hA1, hA2⟩ := hA (m + 1) j' j0 φ ω hφ0 hω0
        obtain ⟨S', hS'⟩ := Option.isSome_iff_exists.1 (hA2 ⟨Hi, hHi_feas⟩)
        have hw' : wOpt (A (m + 1) j' j0 φ ω) ≤ ((weight I Hi : ℝ) : WithTop ℝ) := by
          rw [hS']; simp only [wOpt]
          refine le_trans (hA1 S' hS').2.2 ?_
          unfold OPTsingle
          exact Finset.inf_le (by simp [hHi_feas])
        -- conclude
        have hmem : (j', x) ∈ (range (j0 + 2)) ×ˢ (Φ.filter (fun y => y ≤ ϕ)) := by
          simp only [mem_product, mem_range, mem_filter]
          exact ⟨by omega, hxΦ, le_trans hxle (min_le_right _ _)⟩
        have hstep : Ftil I K ξ Φ A (m + 1) (j0 + 1) ϕ ≤
            Ftil I K ξ Φ A m j' x + wOpt (A (m + 1) j' j0 (phiReq I K ξ ϕ x)
              ((Ftil I K ξ Φ A m j' x).untopD 0)) := by
          rw [Ftil]
          exact Finset.inf_le (f := fun q => Ftil I K ξ Φ A m q.1 q.2 +
            wOpt (A (m + 1) q.1 j0 (phiReq I K ξ ϕ q.2) ((Ftil I K ξ Φ A m q.1 q.2).untopD 0))) hmem
        refine le_trans hstep ?_
        rw [ikp3_weight_split I K ξ S m, ← hLo, ← hHi, WithTop.coe_add]
        exact add_le_add hIH hw'
  intro m hm j _ ϕ hϕ
  unfold F
  apply Finset.le_inf
  intro S hS
  exact key m hm j ϕ hϕ S (by simpa using hS)
