-- Prove2me | solution 1 for InfoRelaxTS.Asymptotic.allocation_113_123
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-24T23:27:26.530223+00:00
-- url     : https://prove2.me/submissions/e3205d09-48ba-4376-9c1c-04de5e7f6362

import Mathlib
import Definitions.Def_InfoRelaxTS_Asymptotic_Setting

open MeasureTheory ProbabilityTheory Filter Topology
open InfoRelaxTS InfoRelaxTS.Asymptotic

namespace IRS3Alloc

lemma sum_diff_two {K : ℕ} (f g : Fin K → ℝ) (a b : Fin K) (hab : a ≠ b)
    (h : ∀ c, c ≠ a → c ≠ b → g c = f c) :
    ∑ c, g c - ∑ c, f c = (g a - f a) + (g b - f b) := by
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_eq_add a b hab (fun c _ hc => by rw [h c hc.1 hc.2, sub_self])
    (fun h => absurd (Finset.mem_univ a) h) (fun h => absurd (Finset.mem_univ b) h)

lemma key {K : ℕ} [NeZero K] (m : Fin K → ℕ → ℝ) (v : Fin K → ℝ)
    (hm : ∀ a, Tendsto (m a) atTop (𝓝 (v a))) (a b : Fin K) (hab : v b < v a) :
    ∀ᶠ T in atTop, ∀ n ∈ Gap.allocSet K T,
      (∀ n' ∈ Gap.allocSet K T, Gap.allocPayoff m n' ≤ Gap.allocPayoff m n) →
        (∀ c, n c ≤ n b) → False := by
  have hne : a ≠ b := fun h => by rw [h] at hab; exact lt_irrefl _ hab
  set g := v a - v b with hg
  have hgpos : 0 < g := sub_pos.mpr hab
  have ha1 : ∀ᶠ i in atTop, v a - g / 4 < m a i :=
    (hm a).eventually (Ioi_mem_nhds (by linarith))
  have hb1 : ∀ᶠ i in atTop, m b i < v b + g / 4 :=
    (hm b).eventually (Iio_mem_nhds (by linarith))
  obtain ⟨N, hN⟩ := eventually_atTop.1 (ha1.and hb1)
  obtain ⟨L0, hL0⟩ := (hm a).bddBelow_range
  have hL0' : ∀ i, L0 ≤ m a i := fun i => hL0 ⟨i, rfl⟩
  set D := max 0 (v a - g / 4 - L0) with hD
  have hD0 : 0 ≤ D := le_max_left _ _
  have hlow : ∀ i, v a - g / 4 - (if i < N then D else 0) ≤ m a i := by
    intro i
    split_ifs with hi
    · have := le_max_right 0 (v a - g / 4 - L0)
      linarith [hL0' i]
    · have := (hN i (by omega)).1
      linarith
  set C := ⌈2 * N * D / g⌉₊ with hC
  refine eventually_atTop.2 ⟨K * (N + 1 + C), ?_⟩
  intro T hT n hn hopt hmax
  rw [Gap.allocSet, Finset.Nat.mem_antidiagonalTuple] at hn
  have hKpos : 0 < K := Nat.pos_of_ne_zero (NeZero.ne K)
  have hsumle : T ≤ K * n b := by
    rw [← hn]
    calc ∑ c, n c ≤ ∑ _c : Fin K, n b := Finset.sum_le_sum fun c _ => hmax c
      _ = K * n b := by simp
  have hnb : N + 1 + C ≤ n b := by
    have : K * (N + 1 + C) ≤ K * n b := le_trans hT hsumle
    exact Nat.le_of_mul_le_mul_left this hKpos
  set L := n b - N with hL
  have hnbL : n b = N + L := by omega
  have hLC : (C : ℝ) + 1 ≤ L := by
    have : C + 1 ≤ L := by omega
    exact_mod_cast this
  have hCge : 2 * N * D / g ≤ C := Nat.le_ceil _
  have hgain : 0 < (L : ℝ) * (g / 2) - N * D := by
    have h1 : 2 * N * D ≤ (C : ℝ) * g := by
      rwa [div_le_iff₀ hgpos] at hCge
    nlinarith
  set n' : Fin K → ℕ := Function.update (Function.update n b N) a (n a + L) with hn'
  have hn'a : n' a = n a + L := by simp [hn']
  have hn'b : n' b = N := by simp [hn', Function.update_of_ne hne.symm]
  have hn'c : ∀ c, c ≠ a → c ≠ b → n' c = n c := by
    intro c hca hcb
    simp [hn', Function.update_of_ne hca, Function.update_of_ne hcb]
  have hmem : n' ∈ Gap.allocSet K T := by
    rw [Gap.allocSet, Finset.Nat.mem_antidiagonalTuple]
    have h := sum_diff_two (fun c => (n c : ℝ)) (fun c => (n' c : ℝ)) a b hne
      (fun c hca hcb => by simp [hn'c c hca hcb])
    simp only [hn'a, hn'b] at h
    have h2 : ((∑ c, n' c : ℕ) : ℝ) = ((∑ c, n c : ℕ) : ℝ) := by
      push_cast
      have : ((n a + L : ℕ) : ℝ) - n a + ((N : ℝ) - n b) = 0 := by
        rw [hnbL]; push_cast; ring
      linarith
    rw [← hn]; exact_mod_cast h2
  have hle := hopt n' hmem
  have hdiff := sum_diff_two (fun c => ∑ i ∈ Finset.range (n c), m c i)
    (fun c => ∑ i ∈ Finset.range (n' c), m c i) a b hne
    (fun c hca hcb => by simp [hn'c c hca hcb])
  simp only [hn'a, hn'b] at hdiff
  rw [Finset.sum_range_add] at hdiff
  rw [hnbL, Finset.sum_range_add] at hdiff
  have hpay : Gap.allocPayoff m n' - Gap.allocPayoff m n =
      ∑ i ∈ Finset.range L, (m a (n a + i) - m b (N + i)) := by
    unfold Gap.allocPayoff
    rw [hdiff, Finset.sum_sub_distrib]; ring
  have hterm : ∀ i ∈ Finset.range L,
      g / 2 - (if i < N then D else 0) ≤ m a (n a + i) - m b (N + i) := by
    intro i _
    have h1 := hlow (n a + i)
    have h2 := (hN (N + i) (by omega)).2
    have h3 : (if n a + i < N then D else 0) ≤ (if i < N then D else 0) := by
      split_ifs <;> first | exact le_refl _ | exact hD0 | omega
    linarith
  have hsum := Finset.sum_le_sum hterm
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
    Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul] at hsum
  have hcard : (((Finset.range L).filter (fun i => i < N)).card : ℝ) ≤ N := by
    have : ((Finset.range L).filter (fun i => i < N)).card ≤ N := by
      calc ((Finset.range L).filter (fun i => i < N)).card
          ≤ (Finset.range N).card := Finset.card_le_card (fun i hi => by
            simp only [Finset.mem_filter, Finset.mem_range] at hi ⊢; exact hi.2)
        _ = N := Finset.card_range N
    exact_mod_cast this
  have : ((Finset.range L).filter (fun i => i < N)).card * D ≤ (N : ℝ) * D :=
    mul_le_mul_of_nonneg_right hcard hD0
  linarith

end IRS3Alloc

theorem solution {K : ℕ} [NeZero K] (m : Fin K → ℕ → ℝ) (v : Fin K → ℝ)
    (hv : Function.Injective v) (hm : ∀ a, Tendsto (m a) atTop (𝓝 (v a))) :
    ∀ᶠ T in atTop, ∀ n ∈ Gap.allocSet K T,
      (∀ n' ∈ Gap.allocSet K T, Gap.allocPayoff m n' ≤ Gap.allocPayoff m n) →
        ∀ b, (∀ c, n c ≤ n b) → ∀ c, v c ≤ v b := by
  obtain ⟨a, ha⟩ := Finite.exists_max v
  have hev : ∀ b : Fin K, ∀ᶠ T in atTop, v b < v a → ∀ n ∈ Gap.allocSet K T,
      (∀ n' ∈ Gap.allocSet K T, Gap.allocPayoff m n' ≤ Gap.allocPayoff m n) →
        (∀ c, n c ≤ n b) → False := by
    intro b
    by_cases hb : v b < v a
    · filter_upwards [IRS3Alloc.key m v hm a b hb] with T hT _ using hT
    · exact Eventually.of_forall fun _ h => absurd h hb
  filter_upwards [eventually_all.2 hev] with T hT n hn hopt b hb c
  by_contra hc
  push_neg at hc
  exact hT b (lt_of_lt_of_le hc (ha c)) n hn hopt hb
