-- Prove2me | solution 1 for Kyprianou.Ch04.exercise49PrefixEventRawMeasurableV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T12:59:29.145449+00:00
-- url     : https://prove2.me/submissions/fd2cbf19-55d7-48c2-a009-361f9e2a09cf

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_exercise49PrefixLowerBoundRationalV1
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch03_CompletedNaturalFiltration
open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
set_option autoImplicit false
/-- The nonnegative prefix and endpoint gain event is raw-past measurable. -/
theorem solution
    {Ω : Type} [MeasurableSpace Ω] (X : NNReal → Ω → ℝ)
    (hc : ∀ ω, IsCadlag (fun t => X t ω)) (s : NNReal) (b : ℝ) :
    MeasurableSet[PerfCorrMSQ.natFiltr X s]
      {ω | (∀ t : NNReal, t ≤ s → 0 ≤ X t ω) ∧ b ≤ X s ω} := by
  have hcoord (t : NNReal) (ht : t ≤ s) :
      Measurable[PerfCorrMSQ.natFiltr X s] (X t) :=
    (comap_measurable (X t)).mono (le_iSup₂_of_le t ht le_rfl) le_rfl
  have hEq : {ω | (∀ t : NNReal, t ≤ s → 0 ≤ X t ω) ∧ b ≤ X s ω} =
      {ω | (0 ≤ X s ω ∧ ∀ q : ℚ, 0 < q → (q : ℝ) < s →
        0 ≤ X (Real.toNNReal q) ω) ∧ b ≤ X s ω} := by
    ext ω
    exact and_congr (Kyprianou.Ch04.exercise49PrefixLowerBoundRationalV1
      (fun t => X t ω) (fun t => (hc ω t).1) s 0) Iff.rfl
  rw [hEq]
  have hR : MeasurableSet[PerfCorrMSQ.natFiltr X s]
      {ω | ∀ q : ℚ, 0 < q → (q : ℝ) < s → 0 ≤ X (Real.toNNReal q) ω} := by
    rw [setOf_forall]
    apply MeasurableSet.iInter
    intro q
    by_cases hq : 0 < q
    · by_cases hqs : (q : ℝ) < s
      · have ht := (Real.toNNReal_lt_iff_lt_coe
          (show (0 : ℝ) < q by exact_mod_cast hq).le).2 hqs
        simpa only [hq, hqs, true_implies] using
          measurableSet_le measurable_const (hcoord _ ht.le)
      · simp [hqs]
    · simp [hq]
  exact (measurableSet_le measurable_const (hcoord s le_rfl)).inter hR |>.inter
    (measurableSet_le measurable_const (hcoord s le_rfl))
