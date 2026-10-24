-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.cutoff_integrable
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T13:02:19.701953+00:00
-- url     : https://prove2.me/submissions/7ca3fea0-c711-467b-b6bc-d12c90c61e74

import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Function.LocallyIntegrable
open scoped BigOperators
open MeasureTheory

theorem solution
    (m : Nat) (T : Real) (hT : 0 < T) :
    MeasureTheory.Integrable (fun t : Real =>
      if 0 ≤ t ∧ t < T then ((T - t) / T) ^ m else 0) MeasureTheory.volume := by
  let g : Real → Real := fun t => ((T - t) / T) ^ m
  have hg : Continuous g := by
    dsimp [g]
    fun_prop
  have hgIcc : MeasureTheory.IntegrableOn g (Set.Icc 0 T) MeasureTheory.volume := by
    exact hg.integrableOn_Icc
  have hgIco : MeasureTheory.IntegrableOn g (Set.Ico 0 T) MeasureTheory.volume := by
    apply hgIcc.mono_set
    exact Set.Ico_subset_Icc_self
  have hs : MeasurableSet (Set.Ico (0 : Real) T) := measurableSet_Ico
  have hgi : MeasureTheory.Integrable (Set.indicator (Set.Ico (0 : Real) T) g)
      MeasureTheory.volume := hgIco.integrable_indicator hs
  convert hgi using 1
  funext t
  simp [Set.indicator, Set.mem_Ico, g]