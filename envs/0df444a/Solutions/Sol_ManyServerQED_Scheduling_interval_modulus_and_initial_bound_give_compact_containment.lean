-- Prove2me | solution 1 for ManyServerQED.Scheduling.interval_modulus_and_initial_bound_give_compact_containment
-- status  : ACCEPTED   (prove)
-- author  : @Jie Luo
-- created : 2026-11-26T04:13:57.448911+00:00
-- url     : https://prove2.me/submissions/cd3f7c46-8929-4903-a017-62ffe7edf338

import Mathlib
open Filter Topology Set MeasureTheory
open scoped ENNReal NNReal
set_option maxHeartbeats 1450000 in
theorem solution {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E]
    (P : Measure Ω) (X : ℕ → Ω → ℝ → E) (T : ℝ) (hT : 0 ≤ T)
    (C : ℝ) (hC : 0 ≤ C) (h0 : ∀ᶠ n in atTop, ∀ ω, ‖X n ω 0‖ ≤ C)
    (hM : ∀ η : ℝ, 0 < η → ∃ δ > (0:ℝ), ∀ᶠ n in atTop,
      P {ω | ∃ s ∈ Icc (0:ℝ) T, ∃ t ∈ Icc (0:ℝ) T, |s-t| ≤ δ ∧
        1 ≤ ‖X n ω s-X n ω t‖} ≤ ENNReal.ofReal η) :
    ∀ η : ℝ, 0 < η → ∃ A ≥ (0:ℝ), ∀ᶠ n in atTop,
      P {ω | ∃ t ∈ Icc (0:ℝ) T, A < ‖X n ω t‖} ≤ ENNReal.ofReal η := by
  intro η hη
  obtain ⟨δ,hδ,hM⟩ := hM η hη
  obtain ⟨N,hN⟩ := exists_nat_gt (T/δ)
  let K := N+1
  have hK : 0 < (K:ℝ) := by dsimp [K]; positivity
  have hKt : T / (K:ℝ) ≤ δ := by
    apply (div_le_iff₀ hK).2
    have hh := (div_lt_iff₀ hδ).1 hN
    have h : (N:ℝ) ≤ (K:ℝ) := by exact_mod_cast Nat.le_succ N
    exact hh.le.trans (by rw [mul_comm δ]; exact mul_le_mul_of_nonneg_right h hδ.le)
  refine ⟨C+K,by positivity,?_⟩
  filter_upwards [h0,hM] with n hn hMod
  refine (measure_mono ?_).trans hMod
  rintro ω ⟨b,hb,hBad⟩
  by_contra h
  let t (j : ℕ) := b*(j:ℝ)/(K:ℝ)
  have ht (j : ℕ) (hj : j ≤ K) : t j ∈ Icc (0:ℝ) T := by
    refine ⟨div_nonneg (mul_nonneg hb.1 (Nat.cast_nonneg _)) hK.le,?_⟩
    have hB : t j ≤ b := by
      apply (div_le_iff₀ hK).2
      exact mul_le_mul_of_nonneg_left (by exact_mod_cast hj) hb.1
    exact hB.trans hb.2
  have hstep (j : ℕ) (hj : j+1 ≤ K) : |t (j+1)-t j| ≤ δ := by
    have he : t (j+1)-t j = b/(K:ℝ) := by
      dsimp [t]
      rw [← sub_div,Nat.cast_add,Nat.cast_one]
      ring
    rw [he,abs_of_nonneg (div_nonneg hb.1 hK.le)]
    exact (div_le_div_of_nonneg_right hb.2 hK.le).trans hKt
  have hd (j : ℕ) (hj : j+1 ≤ K) : ‖X n ω (t (j+1))-X n ω (t j)‖ ≤ 1 := by
    by_contra! hn
    exact h ⟨t (j+1),ht _ hj,t j,ht _ (Nat.le_of_succ_le hj),hstep j hj,hn.le⟩
  have u (j : ℕ) (hj : j ≤ K) : ‖X n ω (t j)‖ ≤ C+(j:ℝ) := by
    induction j with
    | zero => simpa [t] using hn ω
    | succ j ih =>
      have he : X n ω (t (j+1)) = (X n ω (t (j+1))-X n ω (t j))+X n ω (t j) :=
        (sub_add_cancel _ _).symm
      rw [he,Nat.cast_succ]
      have hb := (norm_add_le _ _).trans (add_le_add (hd j hj) (ih (Nat.le_of_succ_le hj)))
      linarith
  have htK : t K = b := mul_div_cancel_right₀ _ hK.ne'
  have hh := u K le_rfl
  rw [htK] at hh
  exact (not_lt_of_ge hh) hBad
