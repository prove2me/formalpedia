-- Prove2me | solution 1 for Kyprianou.Ch04.smallJumpReciprocalQuadraticTailV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T21:17:14.977729+00:00
-- url     : https://prove2.me/submissions/28ea75ed-de41-4cca-871c-318819a3dade

import Mathlib
import Definitions.Def_LeanLevy_Levy_LevyMeasure
import Theorems.Thm_Kyprianou_Ch04_smallJumpQuadraticTailV1
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology
set_option autoImplicit false

/-- Reciprocal cutoff sequence used in continuous-tail comparison. -/
theorem solution (ν : Measure ℝ) (hν : IsLevyMeasure ν) :
    Tendsto (fun n : ℕ => ∫⁻ z in {z : ℝ | |z| ≤ 1 / ((n : ℝ) + 2)},
      ENNReal.ofReal (z ^ 2) ∂ν) atTop (𝓝 0) := by
  let B : ℕ → Set ℝ := fun n => {z | |z| ≤ 1 / ((n : ℝ) + 2)}
  have hden (n : ℕ) : 0 < (n : ℝ) + 2 := by positivity
  have hB (n : ℕ) : MeasurableSet (B n) :=
    measurableSet_le measurable_id.abs measurable_const
  have hSub (n : ℕ) : B n ⊆ Ioo (-1 : ℝ) 1 := by
    intro z hz
    change |z| ≤ 1 / ((n : ℝ) + 2) at hz
    have hr : 1 / ((n : ℝ) + 2) < 1 := (div_lt_iff₀ (hden n)).2 (by nlinarith [Nat.cast_nonneg (α := ℝ) n])
    exact abs_lt.mp (hz.trans_lt hr)
  have hAnti : Antitone B := by
    intro n m hnm z hz
    change |z| ≤ 1 / ((m : ℝ) + 2) at hz
    change |z| ≤ 1 / ((n : ℝ) + 2)
    exact hz.trans (one_div_le_one_div_of_le (hden n) (by exact_mod_cast Nat.add_le_add_right hnm 2))
  have hInter : (⋂ n, B n) ⊆ ({0} : Set ℝ) := by
    intro z hz
    rw [mem_singleton_iff]
    by_contra hn
    have hp : 0 < |z| := abs_pos.mpr hn
    obtain ⟨n, hn⟩ := exists_nat_gt (1 / |z|)
    have h := mem_iInter.mp hz n
    change |z| ≤ 1 / ((n : ℝ) + 2) at h
    have hh := (le_div_iff₀ (hden n)).mp h
    have hnn := (div_lt_iff₀ hp).mp hn
    nlinarith
  exact Kyprianou.Ch04.smallJumpQuadraticTailV1 ν hν B hB hSub hAnti hInter
