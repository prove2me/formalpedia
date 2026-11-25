-- Prove2me | solution 1 for Kyprianou.Ch04.kw47_contact_exp_integral_one
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T21:03:31.964186+00:00
-- url     : https://prove2.me/submissions/913d18d5-cc07-4521-a12e-b7b7cafdc05e

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_kw47_runningSup_contact_measure
import Theorems.Thm_AvramDividend_Classical_runningSup_monotone_and_path_le
open MeasureTheory ProbabilityTheory AvramDividend.Classical Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false

/-- On the continuous Stieltjes contact measure of a spectrally
negative running maximum, the reflected exponential is one a.e. -/
theorem solution
    {Ω : Type} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {F : Filtration NNReal mΩ}
    (L : SpectrallyNegativeLevy P F) (w : Ω)
    (alpha : Real) (T : Real) :
    (∫ s in Set.Ioc (0 : Real) T,
      Real.exp (-alpha * (runningSup L s.toNNReal w -
        L.X s.toNNReal w)) ∂(dividendMeasure (runningSup L) w)) =
    (∫ _s in Set.Ioc (0 : Real) T,
      (1 : Real) ∂(dividendMeasure (runningSup L) w)) := by
  let μ := dividendMeasure (runningSup L) w
  let C : Set Real := {s | 0 ≤ s ∧
    L.X s.toNNReal w < runningSup L s.toNNReal w}
  have hNull : μ C = 0 :=
    Kyprianou.Ch04.kw47_runningSup_contact_measure L w
  have hAe : ∀ᵐ s ∂μ, s ∉ C := by
    rw [ae_iff]
    simpa only [not_not, Set.ofPred_mem_eq] using hNull
  apply integral_congr_ae
  have hAeR := ae_restrict_le (s := Set.Ioc (0 : Real) T) hAe
  filter_upwards [hAeR, ae_restrict_mem measurableSet_Ioc] with s hs hIn
  have hLe : L.X s.toNNReal w ≤ runningSup L s.toNNReal w :=
    (runningSup_monotone_and_path_le L w).2 s.toNNReal
  have hNot : ¬ L.X s.toNNReal w < runningSup L s.toNNReal w := by
    intro hLt
    exact hs ⟨le_of_lt hIn.1, hLt⟩
  have heq : runningSup L s.toNNReal w = L.X s.toNNReal w :=
    le_antisymm (le_of_not_gt hNot) hLe
  simp [heq]
