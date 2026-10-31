-- Prove2me | solution 1 for IncrKnapsack.PTAS.lemma_8
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T03:09:01.44804+00:00
-- url     : https://prove2.me/submissions/2f75c734-b1f1-4623-a9df-9f370287f0d1

import Mathlib
import Definitions.Def_IncrKnapsack_PTAS_Model
import Theorems.Thm_IncrKnapsack_PTAS_representation_1

open Classical
open Finset BigOperators
open IncrKnapsack.PTAS

/-- Between two good periods in different clusters lies a full bad interval. -/
theorem ikp8_gap (I : Instance) (K ξ : ℕ) (s t : Fin I.T) (hs : IsGood I K ξ s)
    (hlt : clus I K ξ s < clus I K ξ t) : ivl I K s + 2 ≤ ivl I K t := by
  by_contra hcon
  push_neg at hcon
  have : ((Finset.Ico 1 (ivl I K t + 1)).filter (fun m => m % K = ξ)) ⊆
      ((Finset.Ico 1 (ivl I K s + 1)).filter (fun m => m % K = ξ)) := by
    intro m hm
    simp only [mem_filter, mem_Ico] at hm ⊢
    refine ⟨⟨hm.1.1, ?_⟩, hm.2⟩
    by_contra h
    have hm' : m = ivl I K s + 1 := by omega
    exact hs (hm' ▸ hm.2)
  have := Finset.card_le_card this
  unfold clus at hlt; omega

theorem ikp8_ivl_lower (I : Instance) (hI : I.Standing) (K : ℕ) (hK : 4 < K) (t : Fin I.T)
    (ht : 0 < lamPlus I t) :
    (eps K / (I.n : ℝ)) ^ (ivl I K t + 1) * lamTotal I < lamPlus I t := by
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
  have hex : ∃ k : ℕ, (eps K / (I.n : ℝ)) ^ (k + 1) * lamTotal I < lamPlus I t := by
    obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one (div_pos ht hLT) hr1
    refine ⟨k, ?_⟩
    have : (eps K / (I.n : ℝ)) ^ (k + 1) ≤ (eps K / (I.n : ℝ)) ^ k :=
      pow_le_pow_of_le_one hr0.le hr1.le (by omega)
    rw [lt_div_iff₀ hLT] at hk
    nlinarith
  unfold ivl; rw [dif_pos hex]
  exact Nat.find_spec hex

theorem ikp8_ivl_upper (I : Instance) (K : ℕ) (t : Fin I.T) (h1 : 1 ≤ ivl I K t) :
    lamPlus I t ≤ (eps K / (I.n : ℝ)) ^ (ivl I K t) * lamTotal I := by
  by_cases hex : ∃ k : ℕ, (eps K / (I.n : ℝ)) ^ (k + 1) * lamTotal I < lamPlus I t
  · have hiv : ivl I K t = Nat.find hex := by unfold ivl; rw [dif_pos hex]
    have := Nat.find_min hex (show ivl I K t - 1 < Nat.find hex by omega)
    push_neg at this
    rwa [show ivl I K t - 1 + 1 = ivl I K t by omega] at this
  · have : ivl I K t = 0 := by unfold ivl; rw [dif_neg hex]
    omega

theorem solution (I : Instance) (hI : I.Standing) (K : ℕ) (hK : 4 < K) (ξ : ℕ) (hξ : ξ < K)
    (Shat : Sol I) (hgood : ∀ i t, Shat i = some t → IsGood I K ξ t) :
    UncrossingStars I K ξ (filt I K (pr I K) Shat) := by
  have hKpos : (0 : ℝ) < K := by exact_mod_cast (by omega : 0 < K)
  have hn : (1 : ℝ) ≤ I.n := by exact_mod_cast hI.n_pos
  have he0 : 0 < eps K := by unfold eps; positivity
  have hr0 : 0 < eps K / (I.n : ℝ) := by positivity
  have hr1 : eps K / (I.n : ℝ) ≤ 1 := by
    rw [div_le_one (by linarith)]; unfold eps
    rw [div_le_iff₀ hKpos]
    have : (5 : ℝ) ≤ K := by exact_mod_cast (by omega : 5 ≤ K)
    nlinarith
  have hpr : ∀ i, 0 < pr I K i := fun i => by unfold pr; positivity
  have hlam : ∀ t, 0 ≤ lamPlus I t := by
    intro t; unfold lamPlus; exact Finset.sum_nonneg (fun τ _ => hI.lam_nonneg τ)
  have hitem : ∀ i, 0 ≤ psiItem I (pr I K) Shat i := by
    intro i; unfold psiItem
    split
    · exact mul_nonneg (hpr i).le (hlam _)
    · exact le_refl _
  have hPsi_ge : ∀ j, psiItem I (pr I K) Shat j ≤ Psi I (pr I K) Shat := by
    intro j
    have hrep : Psi I (pr I K) Shat = ∑ i, psiItem I (pr I K) Shat i := representation_1 I _ Shat
    rw [hrep]
    exact Finset.single_le_sum (fun i _ => hitem i) (mem_univ j)
  -- key monotonicity: a kept item in a later cluster has a strictly larger class
  have key : ∀ i j t s, filt I K (pr I K) Shat i = some t → filt I K (pr I K) Shat j = some s →
      clus I K ξ s < clus I K ξ t → cls I K j < cls I K i := by
    intro i j t s hi hj hlt
    unfold filt at hi hj
    split_ifs at hi with hci
    split_ifs at hj with hcj
    push_neg at hci
    have hgs := hgood j s hj
    have hgap := ikp8_gap I K ξ s t hgs hlt
    have hψi : psiItem I (pr I K) Shat i = pr I K i * lamPlus I t := by
      unfold psiItem; rw [hi]
    have hψj : psiItem I (pr I K) Shat j = pr I K j * lamPlus I s := by
      unfold psiItem; rw [hj]
    have hΨj := hPsi_ge j
    have hΨ0 : 0 ≤ Psi I (pr I K) Shat := le_trans (hitem j) hΨj
    -- λ^{t+} > 0
    have hlt0 : 0 < lamPlus I t := by
      have : 0 < pr I K i * lamPlus I t := by
        rw [← hψi]; exact lt_of_le_of_lt (by positivity) hci
      exact pos_of_mul_pos_right this (hpr i).le
    have hls0 : 0 < lamPlus I s := by
      have hΨ0' : 0 ≤ Psi I (pr I K) Shat := le_trans (hitem j) hΨj
      have : 0 < pr I K j * lamPlus I s := by
        rw [← hψj]; push_neg at hcj; exact lt_of_le_of_lt (by positivity) hcj
      exact pos_of_mul_pos_right this (hpr j).le
    have hlow := ikp8_ivl_lower I hI K hK s hls0
    have hup := ikp8_ivl_upper I K t (by omega)
    have hLT0 : 0 ≤ lamTotal I := by
      unfold lamTotal; exact Finset.sum_nonneg (fun τ _ => hI.lam_nonneg τ)
    -- λ^{t+} < (ε/n) λ^{s+}
    have hpow : (eps K / (I.n : ℝ)) ^ (ivl I K t) ≤
        (eps K / (I.n : ℝ)) * (eps K / (I.n : ℝ)) ^ (ivl I K s + 1) := by
      rw [← pow_succ']
      exact pow_le_pow_of_le_one hr0.le hr1 (by omega)
    have hcmp : lamPlus I t < eps K / (I.n : ℝ) * lamPlus I s := by
      calc lamPlus I t ≤ (eps K / (I.n : ℝ)) ^ (ivl I K t) * lamTotal I := hup
        _ ≤ (eps K / (I.n : ℝ)) * (eps K / (I.n : ℝ)) ^ (ivl I K s + 1) * lamTotal I :=
            mul_le_mul_of_nonneg_right hpow hLT0
        _ = (eps K / (I.n : ℝ)) * ((eps K / (I.n : ℝ)) ^ (ivl I K s + 1) * lamTotal I) := by ring
        _ < eps K / (I.n : ℝ) * lamPlus I s := mul_lt_mul_of_pos_left hlow hr0
    -- p̃_i λ^{t+} > (ε/n) Ψ ≥ (ε/n) p̃_j λ^{s+} > p̃_j λ^{t+}
    have h1 : pr I K j * lamPlus I t < pr I K i * lamPlus I t := by
      calc pr I K j * lamPlus I t < pr I K j * (eps K / (I.n : ℝ) * lamPlus I s) :=
            mul_lt_mul_of_pos_left hcmp (hpr j)
        _ = eps K / (I.n : ℝ) * psiItem I (pr I K) Shat j := by rw [hψj]; ring
        _ ≤ eps K / (I.n : ℝ) * Psi I (pr I K) Shat := mul_le_mul_of_nonneg_left hΨj hr0.le
        _ < psiItem I (pr I K) Shat i := hci
        _ = pr I K i * lamPlus I t := hψi
    have h2 : pr I K j < pr I K i := lt_of_mul_lt_mul_right h1 hlt0.le
    unfold pr at h2
    exact (pow_lt_pow_iff_right₀ (by linarith : (1 : ℝ) < 1 + eps K)).1 h2
  constructor
  · intro i j t s hi hj hc
    rcases lt_trichotomy (clus I K ξ t) (clus I K ξ s) with h | h | h
    · have := key j i s t hj hi h; omega
    · exact h
    · have := key i j t s hi hj h; omega
  · intro i j t s hi hj hc
    by_contra h
    push_neg at h
    have := key i j t s hi hj h; omega
