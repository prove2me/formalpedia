-- Prove2me | solution 1 for Kyprianou.Ch04.exercise49SurvivalFromAllPathBlocksV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T13:00:30.879626+00:00
-- url     : https://prove2.me/submissions/2dd74e1a-6c98-4dc2-9846-1a9bd4c1ba06

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_exercise49PrefixBlockAppendV1
import Theorems.Thm_Kyprianou_Ch04_exercise49PrefixSafeFinishV1
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
set_option autoImplicit false
/-- Independent blocks and pathwise survival. -/
theorem solution
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : NNReal → Ω → ℝ) (hX : IsLevyProcess X P)
    (hm : ∀ t, Measurable (X t)) (hc : ∀ ω, IsCadlag (fun t => X t ω))
    (hSafe : ∃ n : ℕ, 0 < P {ω | ∀ t : NNReal, -(n : ℝ) ≤ X t ω})
    (hBlock : ∃ s : NNReal, 0 < s ∧ ∃ a : ℝ, 0 < a ∧
      0 < P {ω | (∀ t : NNReal, t ≤ s → 0 ≤ X t ω) ∧ a ≤ X s ω}) :
    (P {ω | (sInf {v : WithTop NNReal | ∃ t : NNReal,
      v = ↑t ∧ 0 < t ∧ X t ω < 0}) ≠ ⊤}).toReal < 1 := by
  obtain ⟨n, hn⟩ := hSafe
  obtain ⟨s, hs, a, ha, h⟩ := hBlock
  have hpow (k : ℕ) : 0 < P {ω |
      (∀ u : NNReal, u ≤ (k : NNReal) * s → 0 ≤ X u ω) ∧
        (k : ℝ) * a ≤ X ((k : NNReal) * s) ω} := by
    induction k with
    | zero =>
      have he : {ω | (∀ u : NNReal, u ≤ (0 : NNReal) * s → 0 ≤ X u ω) ∧
          (0 : ℝ) * a ≤ X ((0 : NNReal) * s) ω} = univ := by
        ext ω
        simp [hX.start_zero]
      simpa only [Nat.cast_zero, he, measure_univ] using (zero_lt_one : (0 : ℝ≥0∞) < 1)
    | succ k ih =>
      have hk := Kyprianou.Ch04.exercise49PrefixBlockAppendV1 P X hX hm hc
        ((k : NNReal) * s) s ((k : ℝ) * a) a
        (mul_nonneg (Nat.cast_nonneg k) ha.le) ih h
      simpa only [Nat.cast_succ, add_mul, one_mul] using hk
  obtain ⟨k, hk⟩ := exists_nat_gt ((n : ℝ) / a)
  have hk' : (n : ℝ) ≤ (k : ℝ) * a := by
    have hlt := (div_lt_iff₀ ha).mp hk
    linarith
  have hs' : 0 < P {ω | ∀ u : NNReal, -((k : ℝ) * a) ≤ X u ω} :=
    lt_of_lt_of_le hn (measure_mono (fun ω hω u => (neg_le_neg hk').trans (hω u)))
  exact Kyprianou.Ch04.exercise49PrefixSafeFinishV1 P X hX hm hc
    ((k : NNReal) * s) ((k : ℝ) * a) (hpow k) hs'
