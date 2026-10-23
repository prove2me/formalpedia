-- Prove2me | solution 1 for NonstatRL.Oracle.eq24_all_windows
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-22T17:57:13.930983+00:00
-- url     : https://prove2.me/submissions/17ac3399-cf40-4209-85c3-88e1ac7abf60

import Mathlib
import Definitions.Def_FiniteMDPLearning
import Definitions.Def_NonstatRL_Oracle_Model
import Definitions.Def_NonstatRL_Oracle_Trajectory
import Theorems.Thm_NonstatRL_Oracle_eq23_window_bound

open BanditAlgorithm ENNReal MeasureTheory

namespace NonstatRL.Oracle

theorem eq24_one_le_diameter {S A : ℕ} (M : FiniteMDP S A)
    (As : Fin S → Finset (Fin A)) (hS : 0 < S) : 1 ≤ diameter M As := by
  unfold diameter
  refine le_iSup_of_le ⟨0, hS⟩ (le_iSup_of_le ⟨0, hS⟩ (le_iInf fun f => le_iInf fun _ => ?_))
  unfold hitTime
  refine le_trans ?_ (ENNReal.le_tsum 0)
  have hset : {h : MDPTrajectory S A (0 + 1) | ∀ i : Fin (0 + 1), i ≠ 0 → (h i).1 ≠ ⟨0, hS⟩}
      = Set.univ := by
    ext h; simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
    intro i hi; exact absurd (Fin.ext (by omega)) hi
  rw [hset, measure_univ]

theorem eq24_rewardDrift_nonneg {S A : ℕ} (M : ℕ → FiniteMDP S A)
    (As : Fin S → Finset (Fin A)) (q : ℕ) : 0 ≤ rewardDrift M As q := by
  unfold rewardDrift
  apply Real.sSup_nonneg
  rintro d ⟨s, a, -, rfl⟩
  exact abs_nonneg _

theorem eq24_transDrift_nonneg {S A : ℕ} (M : ℕ → FiniteMDP S A)
    (As : Fin S → Finset (Fin A)) (q : ℕ) : 0 ≤ transDrift M As q := by
  unfold transDrift
  apply Real.sSup_nonneg
  rintro d ⟨s, a, -, rfl⟩
  exact Finset.sum_nonneg (fun _ _ => abs_nonneg _)

end NonstatRL.Oracle

open NonstatRL.Oracle

theorem solution {S A : ℕ} (M : ℕ → FiniteMDP S A)
    (As : Fin S → Finset (Fin A)) (hS : 0 < S)
    (hAs : ∀ s, (As s).Nonempty) (T : ℕ) (Dmax : ℝ)
    (hD : ∀ u, u < T → diameter (M u) As ≤ ENNReal.ofReal Dmax)
    (s₁ : Fin S) (π : MDPPolicy S A) (hπ : IsAllowedPolicy As π)
    (W : ℕ) (hW : 1 ≤ W) (hWT : W ≤ T) :
    expectedReward M s₁ π T - 4 * (T : ℝ) * Dmax / (W : ℝ) -
      2 * (W : ℝ) *
        (rewardBudget M As T + 2 * Dmax * transBudget M As T) ≤
      ∑ t ∈ Finset.range T, optGain (M t) As := by
  have hTnat : 0 < T := by omega
  have hD1 : 1 ≤ Dmax := by
    have h1 := le_trans (eq24_one_le_diameter (M 0) As hS) (hD 0 hTnat)
    exact (ENNReal.one_le_ofReal).mp h1
  set μ := nsMeasure M s₁ π T with hμ
  set dr : ℕ → ℝ := fun q => rewardDrift M As q + 2 * Dmax * transDrift M As q with hdr
  have hdr0 : ∀ q, 0 ≤ dr q := fun q => by
    have := eq24_rewardDrift_nonneg M As q
    have := eq24_transDrift_nonneg M As q
    simp only [hdr]; positivity
  set F : ℕ → MDPTrajectory S A T → ℝ := fun e h =>
    ∑ τ : Fin T, if (τ : ℕ) < e then (M τ).r (h τ).1 (h τ).2 else 0 with hF
  -- number of windows
  set K := (T + W - 1) / W with hK
  have hKW1 : K * W ≤ T + W - 1 := Nat.div_mul_le_self _ _
  have hKW2 : T ≤ K * W := by
    have := Nat.lt_div_mul_add (a := T + W - 1) (b := W) (by omega)
    rw [← hK] at this
    have : T + W - 1 < K * W + W := by linarith [this]
    by_contra hc; push_neg at hc
    have : K * W + W ≤ T + W - 1 := by omega
    omega
  have claim : ∀ m, m ≤ K →
      (∫ h, F (min (m * W) T) h ∂μ) - 2 * (m : ℝ) * Dmax -
        2 * (W : ℝ) * ∑ q ∈ Finset.range (min (m * W) (T - 1)), dr q ≤
      ∑ τ ∈ Finset.range (min (m * W) T), optGain (M τ) As := by
    intro m
    induction m with
    | zero =>
      intro _
      simp [hF]
    | succ m ih =>
      intro hm
      have ih := ih (by omega)
      have hmW : m * W < T := by
        have : m * W + W ≤ K * W := by
          have := Nat.mul_le_mul_right W hm; rw [Nat.succ_mul] at this; exact this
        omega
      set t := m * W with ht
      set L := min W (T - t) with hL
      have hL0 : 0 < L := by omega
      have hLe : t + L ≤ T := by omega
      have hmin1 : min ((m + 1) * W) T = t + L := by
        rw [Nat.succ_mul]; omega
      have hmin0 : min t T = t := by omega
      have hmin2 : min t (T - 1) = t := by omega
      have hmin3 : min ((m + 1) * W) (T - 1) = min (t + L) (T - 1) := by
        rw [Nat.succ_mul]; omega
      have h23 := eq23_window_bound M As hS hAs T Dmax hD s₁ π hπ t L hL0 hLe
      rw [hmin0, hmin2] at ih
      rw [hmin1, hmin3]
      -- integral split
      have hint : (∫ h, F (t + L) h ∂μ) = (∫ h, F t h ∂μ) +
          ∫ h, ∑ τ ∈ (Finset.univ.filter fun τ : Fin T =>
            t ≤ (τ : ℕ) ∧ (τ : ℕ) < t + L), (M τ).r (h τ).1 (h τ).2 ∂μ := by
        rw [← integral_add Integrable.of_finite Integrable.of_finite]
        congr 1; funext h
        simp only [hF, Finset.sum_filter, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl; intro τ _
        by_cases h1 : (τ : ℕ) < t
        · have h2 : (τ : ℕ) < t + L := by omega
          simp [h1, h2]
        · by_cases h2 : (τ : ℕ) < t + L
          · simp [h1, h2]
          · simp [h1, h2]
      have hρ : ∑ τ ∈ Finset.range (t + L), optGain (M τ) As =
          ∑ τ ∈ Finset.range t, optGain (M τ) As +
            ∑ τ ∈ Finset.Ico t (t + L), optGain (M τ) As :=
        (Finset.sum_range_add_sum_Ico _ (by omega)).symm
      have hdsum : ∑ q ∈ Finset.range (min (t + L) (T - 1)), dr q =
          ∑ q ∈ Finset.range t, dr q +
            ∑ q ∈ Finset.Ico t (min (t + L) (T - 1)), dr q :=
        (Finset.sum_range_add_sum_Ico _ (by omega)).symm
      have hwin0 : 0 ≤ ∑ q ∈ Finset.Ico t (min (t + L) (T - 1)), dr q :=
        Finset.sum_nonneg fun q _ => hdr0 q
      have hLW : (L : ℝ) ≤ W := by exact_mod_cast (min_le_left W (T - t))
      have hscale : 2 * (L : ℝ) * ∑ q ∈ Finset.Ico t (min (t + L) (T - 1)), dr q ≤
          2 * (W : ℝ) * ∑ q ∈ Finset.Ico t (min (t + L) (T - 1)), dr q := by
        apply mul_le_mul_of_nonneg_right _ hwin0; linarith
      rw [hint, hρ, hdsum]
      push_cast
      simp only [hdr] at h23 hdsum hwin0 hscale ⊢
      nlinarith
  have hK := claim K le_rfl
  have e1 : min (K * W) T = T := by omega
  have e2 : min (K * W) (T - 1) = T - 1 := by omega
  rw [e1, e2] at hK
  have hE : (∫ h, F T h ∂μ) = expectedReward M s₁ π T := by
    unfold expectedReward
    congr 1; funext h
    simp [hF]
  have hBud : rewardBudget M As T + 2 * Dmax * transBudget M As T =
      ∑ q ∈ Finset.range (T - 1), dr q := by
    simp only [rewardBudget, transBudget, hdr, Finset.sum_add_distrib, Finset.mul_sum]
  rw [hE] at hK
  rw [hBud]
  have hWpos : (0 : ℝ) < W := by exact_mod_cast hW
  have hKle : 2 * (K : ℝ) * Dmax ≤ 4 * (T : ℝ) * Dmax / (W : ℝ) := by
    rw [le_div_iff₀ hWpos]
    have : (K : ℝ) * W ≤ 2 * T := by
      have : K * W ≤ 2 * T := by omega
      exact_mod_cast this
    nlinarith
  linarith
