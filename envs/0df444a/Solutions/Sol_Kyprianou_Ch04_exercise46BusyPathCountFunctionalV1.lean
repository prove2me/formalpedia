-- Prove2me | solution 1 for Kyprianou.Ch04.exercise46BusyPathCountFunctionalV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T23:09:37.395289+00:00
-- url     : https://prove2.me/submissions/cb411951-3d85-4d14-a440-5466ad2c7079

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_bv_jump8_turn9_measurable_exact_cadlag_selectors
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_countable_first_candidate_cover_card_eq_dedup_sum
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Filter AvramDividend.Classical Set
open scoped NNReal ENNReal
set_option autoImplicit false
open scoped Topology
theorem solution
    (D : NNReal → (NNReal → Real) → Real)
    (hD : Measurable (fun z : NNReal × (NNReal → Real) => D z.1 z.2)) :
    ∃ C : (NNReal → Real) → ENNReal, Measurable C ∧
      ∀ Y : NNReal → Real,
        (∀ u, ContinuousWithinAt Y (Ici u) u) →
        (∀ u, 0 < u → ∃ l : Real, Tendsto Y (nhdsWithin u (Iio u)) (nhds l)) →
        C Y = (({t : NNReal | 0 < t ∧
          0 < D t Y ∧ D t Y = -(Y t - Function.leftLim Y t)}).encard : ENNReal) := by
  classical
  obtain ⟨time, mark, ht, hm, hsel⟩ := avram_bv_jump8_turn9_measurable_exact_cadlag_selectors
  let A (k : Nat) (Y : NNReal → Real) : Prop :=
    0 < time k Y ∧ 0 < D (time k Y) Y ∧ D (time k Y) Y = -mark k Y ∧
      (∀ j : Nat, j < k → time j Y ≠ time k Y)
  let C (Y : NNReal → Real) : ENNReal := ∑' k : Nat, if A k Y then 1 else 0
  have hM (k : Nat) : Measurable (fun Y => D (time k Y) Y) :=
    hD.comp ((ht k).prodMk measurable_id)
  refine ⟨C, ?_, ?_⟩
  · apply Measurable.ennreal_tsum
    intro k
    apply Measurable.ite _ measurable_const measurable_const
    apply (measurableSet_lt measurable_const (ht k)).inter
    apply (measurableSet_lt measurable_const (hM k)).inter
    apply (measurableSet_eq_fun (hM k) (hm k).neg).inter
    change MeasurableSet {Y : NNReal → Real | ∀ j < k, time j Y ≠ time k Y}
    rw [show {Y : NNReal → Real | ∀ j < k, time j Y ≠ time k Y} =
        ⋂ j : {j : Nat // j < k}, {Y | time j Y ≠ time k Y} by ext Y; simp]
    exact MeasurableSet.iInter fun j => (measurableSet_eq_fun (ht j) (ht k)).compl
  · intro Y hRight hLeft
    obtain ⟨hex, hcover⟩ := hsel Y hRight hLeft
    let S : Set NNReal := {t | 0 < t ∧ 0 < D t Y ∧
      D t Y = -(Y t - Function.leftLim Y t)}
    have hcov : S ⊆ range (fun k => time k Y) := by
      intro t htS
      apply hcover t htS.1
      intro hzero
      have he := htS.2.2
      rw [hzero, neg_zero] at he
      exact (ne_of_gt htS.2.1) he
    rw [avram_wave7_01_countable_first_candidate_cover_card_eq_dedup_sum _ S hcov]
    apply tsum_congr
    intro k
    by_cases hk : 0 < time k Y
    · simp only [C, A, S, mem_setOf_eq, hk, true_and, hex k hk, and_assoc]
    · simp [C, A, S, hk]
