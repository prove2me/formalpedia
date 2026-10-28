-- Prove2me | solution 1 for HyperMatchDelay.Batching.lemma_4
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-27T02:04:00.658991+00:00
-- url     : https://prove2.me/submissions/750e00a3-3409-43ae-9783-e975e33d5f75

import Mathlib
import Definitions.Def_HyperMatchDelay_Batching_Model

namespace HyperMatchDelay.Batching

theorem greedy_foldl_sub (l : List (Finset ℕ)) (A : Finset (Finset ℕ)) :
    A ⊆ l.foldl greedyStep A := by
  induction l generalizing A with
  | nil => exact le_rfl
  | cons x t ih =>
    simp only [List.foldl_cons]
    refine Finset.Subset.trans ?_ (ih _)
    unfold greedyStep
    split_ifs
    · exact Finset.subset_insert _ _
    · exact le_rfl

theorem greedy_foldl_sub2 (l : List (Finset ℕ)) (A : Finset (Finset ℕ)) :
    l.foldl greedyStep A ⊆ A ∪ l.toFinset := by
  induction l generalizing A with
  | nil => simp
  | cons x t ih =>
    simp only [List.foldl_cons]
    refine Finset.Subset.trans (ih _) ?_
    intro y hy
    rw [Finset.mem_union] at hy ⊢
    rcases hy with hy | hy
    · unfold greedyStep at hy
      split_ifs at hy
      · rw [Finset.mem_insert] at hy
        rcases hy with rfl | hy
        · right; simp
        · left; exact hy
      · left; exact hy
    · right; simp at hy ⊢; right; exact hy

theorem greedy_foldl_disj (l : List (Finset ℕ)) (A : Finset (Finset ℕ))
    (hA : ∀ a ∈ A, ∀ b ∈ A, a ≠ b → Disjoint a b) :
    ∀ a ∈ l.foldl greedyStep A, ∀ b ∈ l.foldl greedyStep A, a ≠ b → Disjoint a b := by
  induction l generalizing A with
  | nil => exact hA
  | cons x t ih =>
    simp only [List.foldl_cons]
    apply ih
    unfold greedyStep
    split_ifs with h
    · intro a ha b hb hab
      rw [Finset.mem_insert] at ha hb
      rcases ha with rfl | ha <;> rcases hb with rfl | hb
      · exact absurd rfl hab
      · exact h b hb
      · exact (h a ha).symm
      · exact hA a ha b hb hab
    · exact hA

theorem greedy_foldl_charge (w : Finset ℕ → ℝ) (l : List (Finset ℕ)) (A : Finset (Finset ℕ))
    (hl : l.Pairwise (fun a b => w b ≤ w a))
    (hA : ∀ a ∈ A, ∀ f ∈ l, w f ≤ w a) :
    ∀ f ∈ l, f ∈ l.foldl greedyStep A ∨
      ∃ g ∈ l.foldl greedyStep A, ¬ Disjoint f g ∧ w f ≤ w g := by
  induction l generalizing A with
  | nil => simp
  | cons x t ih =>
    intro f hf
    simp only [List.foldl_cons]
    rw [List.pairwise_cons] at hl
    rcases List.mem_cons.mp hf with rfl | hft
    · by_cases h : ∀ g ∈ A, Disjoint f g
      · left
        refine greedy_foldl_sub t _ ?_
        unfold greedyStep; rw [if_pos h]; exact Finset.mem_insert_self _ _
      · right
        push_neg at h
        obtain ⟨g, hg, hng⟩ := h
        refine ⟨g, greedy_foldl_sub t _ ?_, hng, hA g hg f (List.mem_cons_self)⟩
        unfold greedyStep
        split_ifs
        · exact Finset.mem_insert_of_mem hg
        · exact hg
    · apply ih _ hl.2 _ f hft
      intro a ha f' hf'
      unfold greedyStep at ha
      split_ifs at ha
      · rw [Finset.mem_insert] at ha
        rcases ha with rfl | ha
        · exact hl.1 f' hf'
        · exact hA a ha f' (List.mem_cons_of_mem _ hf')
      · exact hA a ha f' (List.mem_cons_of_mem _ hf')

end HyperMatchDelay.Batching

open HyperMatchDelay.Batching

theorem solution (k : ℕ) (hk : 1 ≤ k) (w : Finset ℕ → ℝ)
    (σ : Finset (Finset ℕ) → List (Finset ℕ)) (hσ : IsSortedOrder w σ)
    (S : Finset (Finset ℕ)) (hS : ∀ e ∈ S, e.card ≤ k ∧ 0 ≤ w e) :
    IsMatching S (greedy σ S) ∧
    ∀ M, IsMatching S M → (1 / (k : ℝ)) * weight w M ≤ weight w (greedy σ S) := by
  obtain ⟨hnd, hts, hpw⟩ := hσ S
  have hsub : greedy σ S ⊆ S := by
    have := greedy_foldl_sub2 (σ S) ∅
    rw [hts] at this
    simpa [greedy] using this
  have hdisj : ∀ a ∈ greedy σ S, ∀ b ∈ greedy σ S, a ≠ b → Disjoint a b :=
    greedy_foldl_disj (σ S) ∅ (by simp)
  refine ⟨⟨hsub, ?_⟩, ?_⟩
  · intro a ha b hb hab
    exact hdisj a ha b hb hab
  · intro M hM
    obtain ⟨hMS, hMd⟩ := hM
    have hcharge := greedy_foldl_charge w (σ S) ∅ hpw (by simp)
    have key : ∀ f ∈ M, ∃ g ∈ greedy σ S, (f = g ∨ ¬ Disjoint f g) ∧ w f ≤ w g := by
      intro f hf
      have hfl : f ∈ σ S := by rw [← List.mem_toFinset, hts]; exact hMS hf
      rcases hcharge f hfl with h | ⟨g, hg, hn, hw⟩
      · exact ⟨f, h, Or.inl rfl, le_rfl⟩
      · exact ⟨g, hg, Or.inr hn, hw⟩
    choose! φ hφ using key
    set G := greedy σ S with hG
    have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
    have step1 : weight w M ≤ ∑ f ∈ M, w (φ f) := by
      unfold weight
      exact Finset.sum_le_sum (fun f hf => (hφ f hf).2.2)
    have hfib : ∀ g ∈ G, (M.filter (fun f => φ f = g)).card ≤ k := by
      intro g hg
      by_cases hge : g = ∅
      · have : M.filter (fun f => φ f = g) ⊆ {g} := by
          intro f hf
          rw [Finset.mem_filter] at hf
          obtain ⟨hfM, hfg⟩ := hf
          have := (hφ f hfM).2.1
          rw [hfg] at this
          rcases this with h | h
          · simp [h]
          · exfalso; apply h; rw [hge]; exact Finset.disjoint_empty_right _
        calc _ ≤ ({g} : Finset (Finset ℕ)).card := Finset.card_le_card this
          _ = 1 := Finset.card_singleton _
          _ ≤ k := hk
      · have hgne : g.Nonempty := Finset.nonempty_iff_ne_empty.mpr hge
        have hnd : ∀ f ∈ M.filter (fun f => φ f = g), ¬ Disjoint f g := by
          intro f hf
          rw [Finset.mem_filter] at hf
          obtain ⟨hfM, hfg⟩ := hf
          have := (hφ f hfM).2.1
          rw [hfg] at this
          rcases this with h | h
          · rw [h]; rw [Finset.disjoint_self_iff_empty]; exact hge
          · exact h
        have hex : ∀ f ∈ M.filter (fun f => φ f = g), ∃ x, x ∈ f ∧ x ∈ g := by
          intro f hf
          have := hnd f hf
          rw [Finset.not_disjoint_iff] at this
          exact this
        choose! ψ hψ using hex
        calc (M.filter (fun f => φ f = g)).card ≤ g.card := by
              apply Finset.card_le_card_of_injOn ψ
              · intro f hf
                exact (hψ f hf).2
              · intro f1 hf1 f2 hf2 h
                by_contra hne
                have hf1' := hf1
                have hf2' := hf2
                simp only [Finset.coe_filter, Set.mem_setOf_eq] at hf1' hf2'
                have hd := hMd hf1'.1 hf2'.1 hne
                have h1 := (hψ f1 hf1).1
                have h2 := (hψ f2 hf2).1
                rw [h] at h1
                exact Finset.disjoint_left.mp hd h1 h2
          _ ≤ k := (hS g (hsub hg)).1
    have step2 : ∑ f ∈ M, w (φ f) ≤ k * weight w G := by
      rw [Finset.sum_comp]
      have himg : M.image φ ⊆ G := by
        intro g hg
        rw [Finset.mem_image] at hg
        obtain ⟨f, hf, rfl⟩ := hg
        exact (hφ f hf).1
      calc ∑ b ∈ M.image φ, (M.filter (fun f => φ f = b)).card • w b
          ≤ ∑ b ∈ G, (M.filter (fun f => φ f = b)).card • w b := by
            apply Finset.sum_le_sum_of_subset_of_nonneg himg
            intro i hi _
            exact nsmul_nonneg (hS i (hsub hi)).2 _
        _ ≤ ∑ b ∈ G, (k : ℝ) * w b := by
            apply Finset.sum_le_sum
            intro b hb
            rw [nsmul_eq_mul]
            exact mul_le_mul_of_nonneg_right (by exact_mod_cast hfib b hb) (hS b (hsub hb)).2
        _ = k * weight w G := by unfold weight; rw [Finset.mul_sum]
    calc (1 / (k : ℝ)) * weight w M ≤ (1 / (k : ℝ)) * (k * weight w G) := by
          apply mul_le_mul_of_nonneg_left (step1.trans step2)
          positivity
      _ = weight w G := by field_simp

