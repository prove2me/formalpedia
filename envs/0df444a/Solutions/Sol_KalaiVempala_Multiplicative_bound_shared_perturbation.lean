-- Prove2me | solution 1 for KalaiVempala.Multiplicative.bound_shared_perturbation
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T05:45:24.371417+00:00
-- url     : https://prove2.me/submissions/e3f496e8-a4eb-429f-95ce-b1a28ed902ee

import Mathlib
import Definitions.Def_OracleRO_ApproxFPL_FPL
import Definitions.Def_KalaiVempala_Additive_Setting
import Definitions.Def_KalaiVempala_Multiplicative_Setting

set_option autoImplicit false
open MeasureTheory OracleRO.ApproxFPL KalaiVempala.Additive

theorem kv_eq4 {n : ℕ} (Dset : Set (Fin n → ℝ))
    (M : (Fin n → ℝ) → (Fin n → ℝ)) (hM : IsArgminOracle Dset M)
    (s : ℕ → Fin n → ℝ) (T : ℕ) :
    ∑ t ∈ Finset.Icc 1 T, M (prefixSum s t) ⬝ᵥ s t ≤
      M (prefixSum s T) ⬝ᵥ prefixSum s T := by
  induction T with
  | zero => simp [prefixSum]
  | succ T ih =>
    have hP : prefixSum s (T + 1) = prefixSum s T + s (T + 1) := by
      simp only [prefixSum]
      rw [Finset.sum_Icc_succ_top (by omega)]
    rw [Finset.sum_Icc_succ_top (by omega)]
    have h1 := (hM (prefixSum s T)).2 (M (prefixSum s (T + 1))) (hM _).1
    calc ∑ t ∈ Finset.Icc 1 T, M (prefixSum s t) ⬝ᵥ s t + M (prefixSum s (T + 1)) ⬝ᵥ s (T + 1)
        ≤ M (prefixSum s T) ⬝ᵥ prefixSum s T + M (prefixSum s (T + 1)) ⬝ᵥ s (T + 1) := by linarith
      _ ≤ M (prefixSum s (T + 1)) ⬝ᵥ prefixSum s T + M (prefixSum s (T + 1)) ⬝ᵥ s (T + 1) := by linarith
      _ = M (prefixSum s (T + 1)) ⬝ᵥ prefixSum s (T + 1) := by rw [hP, dotProduct_add]

theorem kv_tele {n : ℕ} (p : ℕ → Fin n → ℝ) (T : ℕ) :
    ∑ t ∈ Finset.Icc 1 T, (p t - p (t - 1)) = p T - p 0 := by
  induction T with
  | zero => simp
  | succ T ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih]
    simp

theorem kv_prefix {n : ℕ} (s p : ℕ → Fin n → ℝ) (hp0 : p 0 = 0) (T : ℕ) :
    prefixSum (fun t => s t + p t - p (t - 1)) T = prefixSum s T + p T := by
  induction T with
  | zero => simp [prefixSum, hp0]
  | succ T ih =>
    have e1 : prefixSum (fun t => s t + p t - p (t - 1)) (T + 1)
        = prefixSum (fun t => s t + p t - p (t - 1)) T + (s (T + 1) + p (T + 1) - p T) := by
      simp only [prefixSum]
      rw [Finset.sum_Icc_succ_top (by omega)]
      simp
    have e2 : prefixSum s (T + 1) = prefixSum s T + s (T + 1) := by
      simp only [prefixSum]
      rw [Finset.sum_Icc_succ_top (by omega)]
    rw [e1, ih, e2]
    abel

theorem lemma31 {n : ℕ} (Dset : Set (Fin n → ℝ))
    (M : (Fin n → ℝ) → (Fin n → ℝ)) (hM : IsArgminOracle Dset M)
    (Ddiam : ℝ) (hD : ∀ d ∈ Dset, ∀ d' ∈ Dset, ∑ i, |d i - d' i| ≤ Ddiam)
    (s : ℕ → Fin n → ℝ) (T : ℕ) (hT : 0 < T)
    (p : ℕ → Fin n → ℝ) (hp0 : p 0 = 0) :
    ∑ t ∈ Finset.Icc 1 T, M (prefixSum s t + p t) ⬝ᵥ s t ≤
      M (prefixSum s T) ⬝ᵥ prefixSum s T +
        Ddiam * ∑ t ∈ Finset.Icc 1 T, ‖p t - p (t - 1)‖ := by
  set s' : ℕ → Fin n → ℝ := fun t => s t + p t - p (t - 1) with hs'
  have hpre := kv_prefix s p hp0
  have h4 := kv_eq4 Dset M hM s' T
  have hpre' : ∀ t, prefixSum s' t = prefixSum s t + p t := fun t => hpre t
  simp only [hpre'] at h4
  have h5 := (hM (prefixSum s T + p T)).2 (M (prefixSum s T)) (hM _).1
  -- split the left sum
  have hsplit : ∑ t ∈ Finset.Icc 1 T, M (prefixSum s t + p t) ⬝ᵥ s t
      = ∑ t ∈ Finset.Icc 1 T, M (prefixSum s t + p t) ⬝ᵥ s' t
        - ∑ t ∈ Finset.Icc 1 T, M (prefixSum s t + p t) ⬝ᵥ (p t - p (t - 1)) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [← dotProduct_sub]
    congr 1
    simp only [hs']
    abel
  have hlast : M (prefixSum s T) ⬝ᵥ p T
      = ∑ t ∈ Finset.Icc 1 T, M (prefixSum s T) ⬝ᵥ (p t - p (t - 1)) := by
    rw [← dotProduct_sum, kv_tele, hp0, sub_zero]
  have hterm : ∀ t ∈ Finset.Icc 1 T,
      M (prefixSum s T) ⬝ᵥ (p t - p (t - 1)) - M (prefixSum s t + p t) ⬝ᵥ (p t - p (t - 1))
        ≤ Ddiam * ‖p t - p (t - 1)‖ := by
    intro t _
    rw [← sub_dotProduct, dotProduct]
    calc ∑ i, (M (prefixSum s T) - M (prefixSum s t + p t)) i * (p t - p (t - 1)) i
        ≤ ∑ i, |M (prefixSum s T) i - M (prefixSum s t + p t) i| * ‖p t - p (t - 1)‖ := by
          refine Finset.sum_le_sum fun i _ => ?_
          calc _ ≤ |(M (prefixSum s T) - M (prefixSum s t + p t)) i * (p t - p (t - 1)) i| :=
                le_abs_self _
            _ = |M (prefixSum s T) i - M (prefixSum s t + p t) i| * |(p t - p (t - 1)) i| := by
                rw [abs_mul]; rfl
            _ ≤ _ := by
                gcongr
                exact norm_le_pi_norm (p t - p (t - 1)) i
      _ = (∑ i, |M (prefixSum s T) i - M (prefixSum s t + p t) i|) * ‖p t - p (t - 1)‖ := by
          rw [Finset.sum_mul]
      _ ≤ Ddiam * ‖p t - p (t - 1)‖ := by
          gcongr
          exact hD _ (hM _).1 _ (hM _).1
  have hsum := Finset.sum_le_sum hterm
  rw [Finset.sum_sub_distrib, ← hlast, ← Finset.mul_sum] at hsum
  have h6 : M (prefixSum s T) ⬝ᵥ (prefixSum s T + p T)
      = M (prefixSum s T) ⬝ᵥ prefixSum s T + M (prefixSum s T) ⬝ᵥ p T := dotProduct_add _ _ _
  linarith

theorem solution {n : ℕ} (Dset : Set (Fin n → ℝ))
    (M : (Fin n → ℝ) → (Fin n → ℝ)) (hM : KalaiVempala.Additive.IsArgminOracle Dset M)
    (Ddiam : ℝ) (hD : ∀ d ∈ Dset, ∀ d' ∈ Dset, ∑ i, |d i - d' i| ≤ Ddiam)
    (s : ℕ → Fin n → ℝ) (T : ℕ) (p₁ : Fin n → ℝ) :
    ∑ t ∈ Finset.Icc 1 T, M (prefixSum s t + p₁) ⬝ᵥ s t ≤
      M (prefixSum s T) ⬝ᵥ prefixSum s T + Ddiam * ‖p₁‖ := by
  rcases Nat.eq_zero_or_pos T with hT | hT
  · subst hT
    have h0 : 0 ≤ Ddiam := by
      have := hD _ (hM 0).1 _ (hM 0).1
      simpa using this
    simp [prefixSum]
    exact mul_nonneg h0 (norm_nonneg _)
  · set p : ℕ → Fin n → ℝ := fun t => if t = 0 then 0 else p₁ with hp
    have h := lemma31 Dset M hM Ddiam hD s T hT p (by simp [hp])
    have hsum : ∑ t ∈ Finset.Icc 1 T, ‖p t - p (t - 1)‖ = ‖p₁‖ := by
      rw [Finset.sum_eq_single 1]
      · simp [hp]
      · intro t ht h1
        have ht1 : 1 ≤ t := (Finset.mem_Icc.mp ht).1
        have : t - 1 ≠ 0 := by omega
        have : t ≠ 0 := by omega
        simp [hp, *]
      · intro h; exact absurd (Finset.mem_Icc.mpr ⟨le_rfl, hT⟩) h
    rw [hsum] at h
    have e : ∀ t ∈ Finset.Icc 1 T, M (prefixSum s t + p t) ⬝ᵥ s t = M (prefixSum s t + p₁) ⬝ᵥ s t := by
      intro t ht
      have : t ≠ 0 := by have := (Finset.mem_Icc.mp ht).1; omega
      simp [hp, this]
    rw [Finset.sum_congr rfl e] at h
    exact h
