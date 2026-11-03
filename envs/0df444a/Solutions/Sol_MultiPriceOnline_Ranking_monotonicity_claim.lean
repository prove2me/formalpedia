-- Prove2me | solution 1 for MultiPriceOnline.Ranking.monotonicity_claim
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-02T21:38:17.383407+00:00
-- url     : https://prove2.me/submissions/94a56e4b-6190-44d0-8cb4-c90f985e6216

import Mathlib
import Definitions.Def_MultiPriceOnline_Ranking_LP
import Definitions.Def_MultiPriceOnline_Ranking_Setting

open MultiPriceOnline.Ranking Finset

private lemma offer_some_spec {n T : ℕ} {m : Fin n → ℕ} {r α : Fin n → ℕ → ℝ}
    {sel : Selector n T} (hsel : IsArgmaxSelector sel)
    {t : Fin T} {q : Fin n → ℕ → ℝ} {W : Fin n → ℝ} {A : Finset (Fin n)} {c : Fin n}
    (ho : offer m r α sel t q W A = some c) :
    c ∈ A ∧ 0 < score m r α q W c ∧ ∀ x ∈ A, score m r α q W x ≤ score m r α q W c := by
  unfold offer at ho
  split_ifs at ho with hA hpos
  injection ho with heq
  subst heq
  have h := hsel t A hA (score m r α q W)
  exact ⟨h.1, hpos, h.2⟩

private lemma offer_none_spec {n T : ℕ} {m : Fin n → ℕ} {r α : Fin n → ℕ → ℝ}
    {sel : Selector n T} (hsel : IsArgmaxSelector sel)
    {t : Fin T} {q : Fin n → ℕ → ℝ} {W : Fin n → ℝ} {A : Finset (Fin n)}
    (ho : offer m r α sel t q W A = none) :
    ∀ x ∈ A, score m r α q W x ≤ 0 := by
  intro x hx
  have hA : A.Nonempty := ⟨x, hx⟩
  unfold offer at ho
  rw [dif_pos hA] at ho
  split_ifs at ho with hpos
  have h := (hsel t A hA (score m r α q W)).2 x hx
  linarith

private lemma offer_eq_some_of_subset {n T : ℕ} {m : Fin n → ℕ} {r α : Fin n → ℕ → ℝ}
    {p : Fin T → Fin n → ℕ → ℝ} {sel : Selector n T} (hsel : IsArgmaxSelector sel)
    {W : Fin n → ℝ} (hNT : NoTies m r α p W)
    {t : Fin T} {B C : Finset (Fin n)} (hBC : B ⊆ C) {c : Fin n}
    (hoC : offer m r α sel t (p t) W C = some c) (hcB : c ∈ B) :
    offer m r α sel t (p t) W B = some c := by
  have hc_spec := offer_some_spec hsel hoC
  have hB : B.Nonempty := ⟨c, hcB⟩
  set b := sel t B hB (score m r α (p t) W)
  have hb_spec := hsel t B hB (score m r α (p t) W)
  have hsc_cb : score m r α (p t) W c ≤ score m r α (p t) W b := hb_spec.2 c hcB
  have hsc_bc : score m r α (p t) W b ≤ score m r α (p t) W c := hc_spec.2.2 b (hBC hb_spec.1)
  have hpos_b : 0 < score m r α (p t) W b := lt_of_lt_of_le hc_spec.2.1 hsc_cb
  have h_eq : b = c := by
    by_contra hne
    have h_ne_sc := hNT t b c hne hpos_b
    exact h_ne_sc (le_antisymm hsc_bc hsc_cb)
  unfold offer
  rw [dif_pos hB, if_pos hpos_b]
  exact congrArg some h_eq

private lemma availBefore_subset {n T : ℕ} {m : Fin n → ℕ} {r α : Fin n → ℕ → ℝ}
    {p : Fin T → Fin n → ℕ → ℝ} {sel : Selector n T} (hsel : IsArgmaxSelector sel)
    {W : Fin n → ℝ} (hNT : NoTies m r α p W)
    {P₁ P₂ : Finset (Fin n)} (hP : P₁ ⊆ P₂) :
    ∀ s : ℕ, availBefore m r α p sel P₁ W s ⊆ availBefore m r α p sel P₂ W s := by
  intro s
  induction s with
  | zero => exact hP
  | succ s ih =>
    unfold availBefore
    split_ifs with hs
    · set t₀ : Fin T := ⟨s, hs⟩
      set B := availBefore m r α p sel P₁ W s
      set C := availBefore m r α p sel P₂ W s
      have hB_next_sub : (match offer m r α sel t₀ (p t₀) W B with
          | some j => B.erase j
          | none => B) ⊆ B := by
        cases offer m r α sel t₀ (p t₀) W B with
        | none => exact Subset.rfl
        | some j => exact erase_subset j B
      rcases hoC : offer m r α sel t₀ (p t₀) W C with _ | c
      · exact Subset.trans hB_next_sub ih
      · by_cases hcB : c ∈ B
        · have hoB := offer_eq_some_of_subset hsel hNT ih hoC hcB
          rw [hoB]
          exact erase_subset_erase c ih
        · intro y hy
          have hyB : y ∈ B := hB_next_sub hy
          rw [mem_erase]
          exact ⟨fun heq => hcB (heq ▸ hyB), ih hyB⟩
    · exact ih

theorem solution {n T : ℕ} (m : Fin n → ℕ) (r α : Fin n → ℕ → ℝ)
    (_hr : ∀ i, IsPriceSet (m i) (r i))
    (_hα : ∀ i, MultiPriceOnline.Balance.IsBookingLimits (m i) (r i) (α i))
    (p : Fin T → Fin n → ℕ → ℝ) (_hp : IsDeterministic m p)
    (sel : Selector n T) (hsel : IsArgmaxSelector sel)
    (W : Fin n → ℝ) (_hW : ∀ i, W i ∈ Set.Icc (0 : ℝ) 1) (hNT : NoTies m r α p W)
    (t : Fin T) (i : Fin n) :
    Zt m r α p sel (Finset.univ.erase i) W t ≤ Zt m r α p sel Finset.univ W t := by
  have hsub := availBefore_subset hsel hNT (erase_subset i univ) t.val
  set B := availBefore m r α p sel (univ.erase i) W t.val
  set C := availBefore m r α p sel univ W t.val
  unfold Zt run2
  change (match offer m r α sel t (p t) W B with | some j => score m r α (p t) W j | none => 0) ≤
    (match offer m r α sel t (p t) W C with | some j => score m r α (p t) W j | none => 0)
  rcases hoB : offer m r α sel t (p t) W B with _ | b
  · rcases hoC : offer m r α sel t (p t) W C with _ | c
    · exact le_rfl
    · exact le_of_lt (offer_some_spec hsel hoC).2.1
  · have hb_spec := offer_some_spec hsel hoB
    rcases hoC : offer m r α sel t (p t) W C with _ | c
    · have hle0 := offer_none_spec hsel hoC b (hsub hb_spec.1)
      linarith
    · have hc_spec := offer_some_spec hsel hoC
      exact hc_spec.2.2 b (hsub hb_spec.1)
