-- Prove2me | solution 1 for MultiPriceOnline.Hardness.lemma_4
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T07:57:23.001196+00:00
-- url     : https://prove2.me/submissions/fc78e58b-41af-48df-ba08-efab6b37cf19

import Mathlib
import Definitions.Def_MultiPriceOnline_Hardness_PriceSet
import Definitions.Def_MultiPriceOnline_Hardness_Model
import Definitions.Def_MultiPriceOnline_Hardness_Instance
import Theorems.Thm_MultiPriceOnline_Hardness_lemma_4_counts
import Theorems.Thm_MultiPriceOnline_Hardness_lemma_4_optimization

open Finset MeasureTheory MultiPriceOnline.Hardness

theorem solution {m : ℕ} {r α B : ℕ → ℝ} (hm : 1 ≤ m) (hr : MultiPriceOnline.Balance.IsPriceSet m r)
    (hα : MultiPriceOnline.Balance.IsBookingLimits m r α) (hB : IsPhaseB m r α B) (k : ℕ) (hk : 1 ≤ k)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n →
      ∀ {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (alg : Ω → OnlineAlg n),
        (∀ π : Equiv.Perm (Fin n),
          Measurable (fun ω => revenue k m r (alg ω) (hardInstance n k m B π))) →
        ((Nat.factorial n : ℝ))⁻¹ * ∑ π : Equiv.Perm (Fin n),
            ∫ ω, revenue k m r (alg ω) (hardInstance n k m B π) ∂μ
          ≤ sSup {v : ℝ | ∃ lam : ℕ → ℝ, (∀ j ∈ Icc 1 m, 0 ≤ lam j) ∧
                (∀ j ∈ Icc 1 (m - 1), lam j ≤ Real.log (B j / B (j + 1))) ∧
                (∑ j ∈ Icc 1 m, lam j) ≤ 1 ∧
                v = ∑ j ∈ Icc 1 m, r j * B j * n * (1 - Real.exp (-lam j)) * k}
            + ε * n * k := by
  obtain ⟨N₀, hN₀⟩ := lemma_4_optimization hm hr hα hB k hk ε hε
  refine ⟨max N₀ 1, ?_⟩
  intro n hn Ω _ μ _ alg hmeas
  have hnN : N₀ ≤ n := le_trans (le_max_left _ _) hn
  have hn1 : 1 ≤ n := le_trans (le_max_right _ _) hn
  set S := sSup {v : ℝ | ∃ lam : ℕ → ℝ, (∀ j ∈ Icc 1 m, 0 ≤ lam j) ∧
                (∀ j ∈ Icc 1 (m - 1), lam j ≤ Real.log (B j / B (j + 1))) ∧
                (∑ j ∈ Icc 1 m, lam j) ≤ 1 ∧
                v = ∑ j ∈ Icc 1 m, r j * B j * n * (1 - Real.exp (-lam j)) * k} with hS
  -- pointwise bound for each deterministic algorithm
  have hpt : ∀ ω, ((Nat.factorial n : ℝ))⁻¹ * ∑ π : Equiv.Perm (Fin n),
      revenue k m r (alg ω) (hardInstance n k m B π) ≤ S + ε * n * k := by
    intro ω
    obtain ⟨q, hq0, hqs, hqt, hrev⟩ := lemma_4_counts hr B n k hn1 (alg ω)
    exact le_trans hrev (hN₀ n hnN q hq0 hqs hqt)
  -- revenue is bounded
  have hrmono : ∀ d j : ℕ, 1 ≤ j → j + d ≤ m → r j ≤ r (j + d) := by
    intro d
    induction d with
    | zero => intro j _ _; simp
    | succ d ih =>
      intro j hj hjd
      have h1 := ih j hj (by omega)
      have h2 := hr.2 (j + d) (by omega) (by omega)
      rw [show j + (d + 1) = j + d + 1 by omega]; linarith
  have hrj : ∀ j, 1 ≤ j → j ≤ m → 0 ≤ r j ∧ r j ≤ r m := by
    intro j hj hjm
    have h1 := hrmono (j - 1) 1 le_rfl (by omega)
    have h2 := hrmono (m - j) j hj (by omega)
    rw [show 1 + (j - 1) = j by omega] at h1
    rw [show j + (m - j) = m by omega] at h2
    exact ⟨le_trans hr.1.le h1, h2⟩
  have hsale : ∀ (a : OnlineAlg n) (A : Arrival n) (stock : Fin n → ℕ) (t : ℕ) (i : Fin n) (j : ℕ),
      sale m a A stock t = some (i, j) → 1 ≤ j ∧ j ≤ m := by
    intro a A stock t i j h
    unfold sale at h
    revert h
    rcases a t (history A t) with _ | ⟨i', j'⟩
    · simp
    · dsimp only
      split_ifs with hc
      · intro h; simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨-, rfl⟩ := h; exact ⟨hc.2.2.1, hc.2.2.2.1⟩
      · simp
  have hbound : ∀ (a : OnlineAlg n) (A : Arrival n),
      |revenue k m r a A| ≤ A.T * r m := by
    intro a A
    unfold revenue
    have : ∀ t ∈ range A.T, |(match sale m a A (stockAt k m a A t) t with
        | some (_, j) => r j
        | none => 0 : ℝ)| ≤ r m := by
      intro t _
      rcases h : sale m a A (stockAt k m a A t) t with _ | ⟨i, j⟩
      · simp; linarith [(hrj 1 le_rfl hm).1, (hrj 1 le_rfl hm).2]
      · obtain ⟨h1, h2⟩ := hsale a A _ t i j h
        obtain ⟨h3, h4⟩ := hrj j h1 h2
        simp only; rw [abs_of_nonneg h3]; exact h4
    calc _ ≤ ∑ t ∈ range A.T, |(match sale m a A (stockAt k m a A t) t with
            | some (_, j) => r j
            | none => 0 : ℝ)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ t ∈ range A.T, r m := Finset.sum_le_sum this
      _ = A.T * r m := by simp
  have hint : ∀ π : Equiv.Perm (Fin n),
      Integrable (fun ω => revenue k m r (alg ω) (hardInstance n k m B π)) μ := by
    intro π
    refine Integrable.of_bound (hmeas π).aestronglyMeasurable ((hardInstance n k m B π).T * r m) ?_
    exact Filter.Eventually.of_forall (fun ω => by
      rw [Real.norm_eq_abs]; exact hbound _ _)
  have hsum : ((Nat.factorial n : ℝ))⁻¹ * ∑ π : Equiv.Perm (Fin n),
      ∫ ω, revenue k m r (alg ω) (hardInstance n k m B π) ∂μ =
      ∫ ω, ((Nat.factorial n : ℝ))⁻¹ * ∑ π : Equiv.Perm (Fin n),
        revenue k m r (alg ω) (hardInstance n k m B π) ∂μ := by
    rw [integral_const_mul, integral_finsetSum _ (fun π _ => hint π)]
  rw [hsum]
  calc ∫ ω, ((Nat.factorial n : ℝ))⁻¹ * ∑ π : Equiv.Perm (Fin n),
        revenue k m r (alg ω) (hardInstance n k m B π) ∂μ
      ≤ ∫ _ω, (S + ε * n * k) ∂μ := by
        apply integral_mono _ (integrable_const _) hpt
        exact (integrable_finsetSum _ (fun π _ => hint π)).const_mul _
    _ = S + ε * n * k := by simp
