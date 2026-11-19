-- Prove2me | solution 1 for LevyStochCalc.Poisson.exists_iSup_setLIntegral_timeSlab_le
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-19T03:05:55.972913+00:00
-- url     : https://prove2.me/submissions/48e4b3aa-50cc-4639-85f9-895d1aa9216e

import Definitions.Def_LevyStochCalc_Poisson_Simplicity_F000

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology
open LevyStochCalc.Poisson

theorem solution {f : ℝ → ℝ≥0∞} (hf : Measurable f)
    (hfin : ∫⁻ x, f x ≠ ⊤) {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ n : ℕ, ⨆ k : ℕ, ∫⁻ x in timeSlab n k, f x ≤ ε := by
  by_cases hε_top : ε = ⊤
  · exact ⟨0, by simp [hε_top]⟩
  have hε2 : (0 : ℝ≥0∞) < ε / 2 := ENNReal.half_pos hε
  have htrunc : Tendsto (fun M : ℕ => ∫⁻ x, (f x - (M : ℝ≥0∞))) atTop (𝓝 0) := by
    have h0 : ∀ᵐ x ∂volume, Tendsto (fun M : ℕ => f x - (M : ℝ≥0∞)) atTop (𝓝 0) := by
      have hae : ∀ᵐ x ∂volume, f x < ⊤ := ae_lt_top hf hfin
      filter_upwards [hae] with x hx
      refine tendsto_atTop_of_eventually_const (i₀ := ⌈(f x).toReal⌉₊ + 1) fun M hM => ?_
      have hle : f x ≤ (M : ℝ≥0∞) := by
        rw [← ENNReal.ofReal_toReal hx.ne, ← ENNReal.ofReal_natCast M]
        exact ENNReal.ofReal_le_ofReal (by
          have : (f x).toReal ≤ (⌈(f x).toReal⌉₊ : ℝ) := Nat.le_ceil _
          exact this.trans (by exact_mod_cast Nat.le_trans (Nat.le_succ _) hM))
      exact tsub_eq_zero_of_le hle
    exact tendsto_lintegral_of_dominated_convergence f
      (fun M => hf.sub measurable_const) (fun M => ae_of_all _ fun x => tsub_le_self)
      hfin h0 |>.trans (by simp)
  rw [ENNReal.tendsto_atTop_zero] at htrunc
  obtain ⟨M, hM⟩ := htrunc (ε / 2) hε2
  have hM_fin : ∫⁻ x, (f x - (M : ℝ≥0∞)) ≤ ε / 2 := hM M le_rfl
  by_cases hM0 : M = 0
  · refine ⟨0, iSup_le fun k => ?_⟩
    have hle : ∫⁻ x in timeSlab 0 k, f x ≤ ∫⁻ x, f x := setLIntegral_le_lintegral _ _
    simp only [hM0, Nat.cast_zero, tsub_zero] at hM_fin
    exact hle.trans (hM_fin.trans ENNReal.half_le_self)
  have hM_pos : (0 : ℝ≥0∞) < (M : ℝ≥0∞) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hM0)
  have hpow : Tendsto (fun n : ℕ => (M : ℝ≥0∞) * ENNReal.ofReal ((1 / 2 : ℝ) ^ n)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun n : ℕ => (1 / 2 : ℝ) ^ n) atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
    have h2 : Tendsto (fun n : ℕ => ENNReal.ofReal ((1 / 2 : ℝ) ^ n)) atTop (𝓝 0) := by
      simpa using ENNReal.tendsto_ofReal h1
    simpa using ENNReal.Tendsto.const_mul h2 (Or.inr (ENNReal.natCast_ne_top M))
  rw [ENNReal.tendsto_atTop_zero] at hpow
  obtain ⟨n, hn⟩ := hpow (ε / 2) hε2
  refine ⟨n, iSup_le fun k => ?_⟩
  have hsplit : ∫⁻ x in timeSlab n k, f x ≤
      ∫⁻ x in timeSlab n k, ((M : ℝ≥0∞) + (f x - (M : ℝ≥0∞))) :=
    setLIntegral_mono' (measurableSet_timeSlab n k) fun x _ => le_add_tsub
  have hadd : ∫⁻ x in timeSlab n k, ((M : ℝ≥0∞) + (f x - (M : ℝ≥0∞))) =
      (∫⁻ _ in timeSlab n k, (M : ℝ≥0∞)) + ∫⁻ x in timeSlab n k, (f x - (M : ℝ≥0∞)) :=
    lintegral_add_left measurable_const _
  have h1 : ∫⁻ _ in timeSlab n k, (M : ℝ≥0∞) ≤ ε / 2 := by
    rw [setLIntegral_const, volume_timeSlab]
    exact hn n le_rfl
  have h2 : ∫⁻ x in timeSlab n k, (f x - (M : ℝ≥0∞)) ≤ ε / 2 :=
    (setLIntegral_le_lintegral _ _).trans hM_fin
  calc ∫⁻ x in timeSlab n k, f x
      ≤ (∫⁻ _ in timeSlab n k, (M : ℝ≥0∞)) + ∫⁻ x in timeSlab n k, (f x - (M : ℝ≥0∞)) :=
        hsplit.trans_eq hadd
    _ ≤ ε / 2 + ε / 2 := add_le_add h1 h2
    _ = ε := ENNReal.add_halves ε
