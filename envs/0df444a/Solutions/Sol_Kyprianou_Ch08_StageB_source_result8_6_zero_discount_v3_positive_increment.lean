-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.source_result8_6_zero_discount_v3_positive_increment
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T21:15:05.725136+00:00
-- url     : https://prove2.me/submissions/923d5854-95c9-4485-8588-5d9aa4719a95

import Mathlib
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Theorems.Thm_Kyprianou_Ch08_StageB_source_result8_6_zero_discount_v3_antitone_of_no_positive_increment
set_option autoImplicit false
open MeasureTheory Filter Set Topology Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal

theorem solution :
    ∀ (Ω : Type) [MeasurableSpace Ω]
      (P : Measure Ω) [IsProbabilityMeasure P]
      (D : SpectrallyNegativeModel Ω P),
      ∃ (t : ℝ≥0) (ε : ℝ), 0 < (t : ℝ) ∧ 0 < ε ∧ P {ω | ε < D.X t ω} ≠ 0 := by
  intro Ω mΩ P hP D
  have hex : ∃ t : ℝ≥0, P {ω | 0 < D.X t ω} ≠ 0 := by
    by_contra h
    push Not at h
    have hant : ∀ᵐ ω ∂P, Antitone (fun t : ℝ≥0 => D.X t ω) :=
      Filter.Eventually.of_forall fun ω => by
        intro u v huv
        exact source_result8_6_zero_discount_v3_antitone_of_no_positive_increment Ω P D h ω u v huv
    exact (D.excludesNegativeSubordinator hant).elim
  rcases hex with ⟨t, ht⟩
  have htpos : (0 : ℝ) < t := by
    by_contra h
    have ht0 : t = 0 := NNReal.coe_eq_zero.mp (le_antisymm (not_lt.mp h) t.2)
    apply ht
    rw [ht0, D.levy.start_zero]
    simp
  rcases (by
    have hU : {ω | 0 < D.X t ω} = ⋃ n : ℕ, {ω | 1 / ((n : ℝ) + 1) < D.X t ω} := by
      ext ω
      simp only [mem_setOf_eq, mem_iUnion]
      constructor
      · intro hω
        obtain ⟨n, hn⟩ := exists_nat_one_div_lt hω
        exact ⟨n, hn⟩
      · rintro ⟨n, hn⟩
        exact lt_trans (by positivity) hn
    by_contra hc
    push Not at hc
    have hci : ∀ n : ℕ, P {ω | 1 / ((n : ℝ) + 1) < D.X t ω} = 0 := by
      intro n
      exact hc (1 / ((n : ℝ) + 1)) (by positivity)
    have hzero : P {ω | 0 < D.X t ω} = 0 := by
      rw [hU]
      exact measure_iUnion_null hci
    exact ht hzero : ∃ ε > 0, P {ω | ε < D.X t ω} ≠ 0) with ⟨ε, hε, hεm⟩
  exact ⟨t, ε, htpos, hε, hεm⟩
