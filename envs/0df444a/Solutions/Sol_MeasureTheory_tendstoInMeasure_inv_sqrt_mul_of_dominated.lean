-- Prove2me | solution 1 for MeasureTheory.tendstoInMeasure_inv_sqrt_mul_of_dominated
-- status  : ACCEPTED   (prove)
-- author  : @LukeBernese
-- created : 2026-08-15T22:16:07.931586+00:00
-- url     : https://prove2.me/submissions/0f27d2f9-19df-4380-b6f2-4004b95f6c28

import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.Analysis.SpecialFunctions.Sqrt

open MeasureTheory Filter
open scoped ENNReal NNReal Topology

set_option maxHeartbeats 1000000

/-- A sequence dominated by a single random variable, scaled by `n^{-1/2}`,
tends to `0` in probability. -/
theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P]
    (W : ℕ → Ω → ℝ) (Z : Ω → ℝ) (hZ : Measurable Z) (hW : ∀ n ω, |W n ω| ≤ Z ω) :
    TendstoInMeasure P (fun (n : ℕ) (ω : Ω) => (Real.sqrt n)⁻¹ * W n ω) atTop 0 := by
  refine tendstoInMeasure_of_ne_top (fun ε hε hεtop => ?_)
  set r : ℝ := ε.toReal with hrdef
  have hrpos : 0 < r := ENNReal.toReal_pos hε.ne' hεtop
  have hZ0 : ∀ ω, 0 ≤ Z ω := fun ω => le_trans (abs_nonneg _) (hW 0 ω)
  have hd : ∀ a : ℝ, (edist a (0:ℝ)).toReal = |a| := by
    intro a
    rw [edist_dist, ENNReal.toReal_ofReal dist_nonneg, Real.dist_eq, sub_zero]
  set t : ℕ → Set Ω := fun n => {ω | r * Real.sqrt n ≤ Z ω} with ht
  have htm : ∀ n, MeasurableSet (t n) := by
    intro n
    rw [ht]
    exact measurableSet_le measurable_const hZ
  -- the level sets sit inside `t n`
  have hsub : ∀ n : ℕ, {ω | ε ≤ edist ((Real.sqrt n)⁻¹ * W n ω) (0 : ℝ)} ⊆ t n := by
    intro n ω hω
    have hω' : r ≤ |(Real.sqrt n)⁻¹ * W n ω| := by
      have := ENNReal.toReal_mono (edist_ne_top ((Real.sqrt n)⁻¹ * W n ω) (0:ℝ)) hω
      rwa [hd] at this
    rw [abs_mul, abs_inv, abs_of_nonneg (Real.sqrt_nonneg _)] at hω'
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp only [Nat.cast_zero, Real.sqrt_zero, inv_zero, zero_mul] at hω'
      linarith
    · have hpos : 0 < Real.sqrt n := Real.sqrt_pos.mpr (by exact_mod_cast hn)
      have hZω : r ≤ (Real.sqrt n)⁻¹ * Z ω :=
        le_trans hω' (by
          have := hW n ω
          exact mul_le_mul_of_nonneg_left this (by positivity))
      have hmul := mul_le_mul_of_nonneg_left hZω hpos.le
      rw [← mul_assoc, mul_inv_cancel₀ hpos.ne', one_mul] at hmul
      simpa [ht, mul_comm] using hmul
  -- `t` is antitone with empty intersection
  have hanti : Antitone t := by
    intro n m hnm ω hω
    have hle : Real.sqrt n ≤ Real.sqrt m := Real.sqrt_le_sqrt (by exact_mod_cast hnm)
    exact le_trans (mul_le_mul_of_nonneg_left hle hrpos.le) hω
  have hempty : (⋂ n, t n) = ∅ := by
    ext ω
    simp only [Set.mem_iInter, Set.mem_empty_iff_false, iff_false, not_forall]
    obtain ⟨n, hn⟩ := exists_nat_gt ((Z ω / r) ^ 2)
    refine ⟨n, ?_⟩
    simp only [ht, Set.mem_setOf_eq, not_le]
    have hlt : Z ω / r < Real.sqrt n := by
      calc Z ω / r = Real.sqrt ((Z ω / r) ^ 2) := by
            rw [Real.sqrt_sq (div_nonneg (hZ0 ω) hrpos.le)]
        _ < Real.sqrt n := Real.sqrt_lt_sqrt (by positivity) hn
    rw [div_lt_iff₀ hrpos] at hlt
    linarith
  -- conclude by continuity from above
  have hten : Tendsto (fun n => P (t n)) atTop (𝓝 (P (⋂ n, t n))) :=
    tendsto_measure_iInter_atTop (fun n => (htm n).nullMeasurableSet) hanti
      ⟨0, measure_ne_top _ _⟩
  rw [hempty, measure_empty] at hten
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hten
    (fun n => by simp) (fun n => measure_mono (hsub n))
