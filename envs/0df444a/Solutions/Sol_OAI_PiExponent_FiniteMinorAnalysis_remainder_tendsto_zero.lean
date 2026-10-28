-- Prove2me | solution 1 for OAI.PiExponent.FiniteMinorAnalysis.remainder_tendsto_zero
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T09:40:14.193973+00:00
-- url     : https://prove2.me/submissions/821445ea-5e90-446e-a22d-dc0205e52128

import Definitions.Def_PiExponent_FiniteTranslationData
import Mathlib

open OAI.PiExponent
open OAI.PiExponent.FiniteMinorAnalysis
open Filter Topology
open scoped BigOperators

namespace S38RT

theorem logH : Tendsto (fun H : Real => Real.log (H + 1) / H) atTop (𝓝 0) := by
  have h := (Real.tendsto_pow_log_div_mul_add_atTop 1 (-1) 1 one_ne_zero).comp
    (tendsto_atTop_add_const_right _ 1 tendsto_id)
  refine h.congr' (Eventually.of_forall fun H => ?_)
  simp

theorem gen (g : Real → Real) (C : Real) (N : Nat) (hC : 0 < C)
    (h : ∀ᶠ H : Real in atTop, 1 ≤ g H ∧ g H ≤ C * (H + 1) ^ N) :
    Tendsto (fun H : Real => Real.log (g H) / H) atTop (𝓝 0) := by
  have hup : Tendsto (fun H : Real => Real.log C * H⁻¹ + N * (Real.log (H + 1) / H)) atTop (𝓝 0) := by
    have := (tendsto_inv_atTop_zero.const_mul (Real.log C)).add (logH.const_mul (N : Real))
    simpa using this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup ?_ ?_
  · filter_upwards [h, eventually_gt_atTop 0] with H hH hpos
    exact div_nonneg (Real.log_nonneg hH.1) hpos.le
  · filter_upwards [h, eventually_gt_atTop 0] with H hH hpos
    have h1 : Real.log (g H) ≤ Real.log C + N * Real.log (H + 1) := by
      calc Real.log (g H) ≤ Real.log (C * (H + 1) ^ N) :=
            Real.log_le_log (by linarith [hH.1]) hH.2
        _ = Real.log C + N * Real.log (H + 1) := by
            rw [Real.log_mul hC.ne' (by positivity), Real.log_pow]
    rw [div_le_iff₀ hpos]
    have : (Real.log C * H⁻¹ + N * (Real.log (H + 1) / H)) * H = Real.log C + N * Real.log (H + 1) := by
      field_simp
    linarith

lemma floor_bound (w H : ℝ) (hw : 0 ≤ w) (hH : 0 ≤ H) :
    ((⌊H / w⌋₊ + 1 : ℕ) : ℝ) ≤ (1 / w + 1) * (H + 1) := by
  push_cast
  have h1 : (⌊H / w⌋₊ : ℝ) ≤ H / w := Nat.floor_le (div_nonneg hH hw)
  have h2 : H / w = H * (1 / w) := by rw [mul_one_div]
  have h3 : 0 ≤ 1 / w := by positivity
  nlinarith

lemma simplex_card {n : ℕ} (w : Fin n → ℝ) (hw : ∀ i, 0 ≤ w i) (H : ℝ) (hH : 0 ≤ H) :
    ((realWeightedSimplex w H).card : ℝ) ≤ (∏ i, (1 / w i + 1)) * (H + 1) ^ n := by
  classical
  have hsub : realWeightedSimplex w H ⊆
      Fintype.piFinset (fun i => Finset.range (⌊H / w i⌋₊ + 1)) := by
    unfold realWeightedSimplex
    convert Finset.filter_subset _ _
  have hc := Finset.card_le_card hsub
  rw [Fintype.card_piFinset] at hc
  simp only [Finset.card_range] at hc
  calc ((realWeightedSimplex w H).card : ℝ) ≤ ((∏ i, (⌊H / w i⌋₊ + 1) : ℕ) : ℝ) := by
        exact_mod_cast hc
    _ = ∏ i, (((⌊H / w i⌋₊ + 1 : ℕ)) : ℝ) := by push_cast; rfl
    _ ≤ ∏ i, ((1 / w i + 1) * (H + 1)) := by
        apply Finset.prod_le_prod
        · intro i _; positivity
        · intro i _; exact floor_bound (w i) H (hw i) hH
    _ = (∏ i, (1 / w i + 1)) * (H + 1) ^ n := by
        rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

lemma log_nat_eq (M : ℕ) : Real.log (M : ℝ) = Real.log (max 1 (M : ℝ)) := by
  rcases Nat.eq_zero_or_pos M with h | h
  · subst h; simp
  · rw [max_eq_right (by exact_mod_cast h)]

end S38RT

open S38RT in
theorem solution
    {m : ℕ} (K : ℕ) (v theta : ℝ) (q : Fin m → ℕ)
    (hK : 0 < K) (hv : 0 < v) (htheta : 0 < theta) (hq : ∀ i, 2 ≤ q i) :
    Tendsto (remainder K v theta q) atTop (𝓝 0) := by
  set w := InterpolationMatrix.rowWeights v theta (MatrixArithmetic.logWeights q) with hwdef
  have hw : ∀ i, 0 ≤ w i := by
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [hwdef, InterpolationMatrix.rowWeights]; exact hv.le
    · simp only [hwdef, InterpolationMatrix.rowWeights, Fin.cases_succ]
      exact div_nonneg (by unfold MatrixArithmetic.logWeights; positivity) htheta.le
  set A := (∏ i, (1 / w i + 1)) with hA
  have hA1 : 1 ≤ A := by
    calc (1 : ℝ) = ∏ _i : Fin (m + 1), (1 : ℝ) := by simp
      _ ≤ A := by
        apply Finset.prod_le_prod (fun _ _ => zero_le_one)
        intro i _
        have : 0 ≤ 1 / w i := by have := hw i; positivity
        linarith
  -- row count
  have hrow : Tendsto (fun H => Real.log (rowCount K v theta q H : ℝ) / H) atTop (𝓝 0) := by
    have := gen (fun H => max 1 (rowCount K v theta q H : ℝ)) ((K + 1) * A) (m + 1)
      (by positivity) ?_
    · refine this.congr' (Eventually.of_forall fun H => ?_)
      simp only; rw [← log_nat_eq]
    filter_upwards [eventually_ge_atTop 0] with H hH
    refine ⟨le_max_left _ _, max_le ?_ ?_⟩
    · have : (1 : ℝ) ≤ (K + 1) * A := by nlinarith
      calc (1 : ℝ) ≤ (K + 1) * A := this
        _ ≤ (K + 1) * A * (H + 1) ^ (m + 1) := by
          apply le_mul_of_one_le_right (by positivity)
          exact one_le_pow₀ (by linarith)
    · have hrc : (rowCount K v theta q H : ℝ) ≤ K * ((strictWeightedSimplex w H).card : ℝ) := by
        unfold rowCount
        rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_coe]; push_cast; rfl
      have hsc : (strictWeightedSimplex w H).card ≤ (realWeightedSimplex w H).card := by
        unfold strictWeightedSimplex; exact Finset.card_filter_le _ _
      have hs := simplex_card w hw H hH
      have hK0 : (0 : ℝ) ≤ K := Nat.cast_nonneg _
      calc (rowCount K v theta q H : ℝ) ≤ K * ((strictWeightedSimplex w H).card : ℝ) := hrc
        _ ≤ K * (A * (H + 1) ^ (m + 1)) := by
          apply mul_le_mul_of_nonneg_left _ hK0
          exact (Nat.cast_le.mpr hsc).trans hs
        _ ≤ (K + 1) * A * (H + 1) ^ (m + 1) := by
          have : 0 ≤ A * (H + 1) ^ (m + 1) := by positivity
          nlinarith
  have hterm : Tendsto (fun H => Real.log (termCount m v H : ℝ) / H) atTop (𝓝 0) := by
    have := gen (fun H => max 1 (termCount m v H : ℝ)) (1 / v + 1) (2 * m + 1)
      (by positivity) ?_
    · refine this.congr' (Eventually.of_forall fun H => ?_)
      simp only; rw [← log_nat_eq]
    filter_upwards [eventually_ge_atTop 0] with H hH
    refine ⟨le_max_left _ _, max_le ?_ ?_⟩
    · have h0 : 0 ≤ 1 / v := by positivity
      have : (1 : ℝ) ≤ 1 / v + 1 := by linarith
      calc (1 : ℝ) ≤ 1 / v + 1 := this
        _ ≤ (1 / v + 1) * (H + 1) ^ (2 * m + 1) := by
          apply le_mul_of_one_le_right (by positivity)
          exact one_le_pow₀ (by linarith)
    · unfold termCount
      push_cast
      have h1 : ((⌊H⌋₊ : ℝ) + 1) ≤ H + 1 := by linarith [Nat.floor_le hH]
      have h2 := floor_bound v H hv.le hH
      push_cast at h2
      calc ((⌊H⌋₊ : ℝ) + 1) ^ (2 * m) * ((⌊H / v⌋₊ : ℝ) + 1)
          ≤ (H + 1) ^ (2 * m) * ((1 / v + 1) * (H + 1)) := by
            apply mul_le_mul (pow_le_pow_left₀ (by positivity) h1 _) h2 (by positivity)
              (by positivity)
        _ = (1 / v + 1) * (H + 1) ^ (2 * m + 1) := by ring
  have hconst : Tendsto (fun H : ℝ => (Real.log 2 / 4 -
      Real.log (1 - Real.exp (-Real.log 2 / 2))) / H) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_id
  have := (hrow.add hconst).add hterm
  simp only [add_zero] at this
  refine this.congr' (Eventually.of_forall fun H => ?_)
  unfold remainder collisionRemainder
  ring
