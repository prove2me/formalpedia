-- Prove2me | solution 1 for Kyprianou.Ch03.closedHitApproximationAELimitV1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T12:35:06.625939+00:00
-- url     : https://prove2.me/submissions/dbe0a3d0-5684-40ce-a1cd-ce64fe5a9beb
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_Kyprianou_Ch03_positiveHitInfDelayedClosedV1
import Theorems.Thm_Kyprianou_Ch03_delayedClosedHitFixedApproxV1
import Theorems.Thm_Kyprianou_Ch03_delayedOpenHitStoppingV1
import Theorems.Thm_Kyprianou_Ch03_completedNaturalLevyFiltrationRightContinuous
import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch03_EntryAndHittingTimes
import Definitions.Def_Kyprianou_Ch03_CompletedNaturalFiltration
open MeasureTheory ProbabilityTheory Filter Set
open Kyprianou.Ch03
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (X : NNReal → Omega → Real)
    (hX : IsLevyProcess X P)
    (hNatural : IsCompletedNaturalFiltration P X F)
    (B : Set Real) (hB : IsClosed B)
    (hStop : ∀ m n : ℕ, IsStoppingTime F (fun w : Omega => sInf {u : WithTop NNReal | ∃ r : NNReal,
      (1 / ((m : NNReal) + 1)) < r ∧
      X r w ∈ Metric.thickening (1 / ((n : ℝ) + 1)) B ∧
      u = (r : WithTop NNReal)})) :
    firstHittingTime X B =ᵐ[P] (fun w : Omega => ⨅ m : ℕ, ⨆ n : ℕ, (fun w : Omega => sInf {u : WithTop NNReal | ∃ r : NNReal,
      (1 / ((m : NNReal) + 1)) < r ∧
      X r w ∈ Metric.thickening (1 / ((n : ℝ) + 1)) B ∧
      u = (r : WithTop NNReal)}) w) := by
  let a (m : ℕ) : NNReal := 1 / ((m : NNReal) + 1)
  let U (m n : ℕ) (w : Omega) := sInf {u : WithTop NNReal | ∃ r : NNReal,
    a m < r ∧ X r w ∈ Metric.thickening (1 / ((n : ℝ) + 1)) B ∧ u = ↑r}
  let V (m n : ℕ) (w : Omega) := sInf ((fun r : NNReal => (r : WithTop NNReal)) ''
    {r : NNReal | a m ≤ r ∧ X r w ∈ Metric.thickening (1 / ((n : ℝ) + 1)) B})
  let C (m : ℕ) (w : Omega) := sInf ((fun r : NNReal => (r : WithTop NNReal)) ''
    {r : NNReal | a m ≤ r ∧ X r w ∈ B})
  have hRC := completedNaturalLevyFiltrationRightContinuous P X hX F hNatural
  have hv (m n : ℕ) : IsStoppingTime F (V m n) :=
    delayedOpenHitStoppingV1 P F X hX hNatural hRC (a m) _
      Metric.isOpen_thickening
  have he (m : ℕ) : ∀ᵐ w ∂P, (⨆ n, V m n w) = C m w :=
    delayedClosedHitFixedApproxV1 P F X hX hNatural B hB (a m)
      (V m) (fun _ _ => rfl) (hv m)
  have hall := ae_all_iff.mpr he
  change ∀ᵐ w ∂P, firstHittingTime X B w = (⨅ m, ⨆ n, U m n w)
  filter_upwards [hall] with w hw
  rw [positiveHitInfDelayedClosedV1 X B w]
  change (⨅ m, C m w) = (⨅ m, ⨆ n, U m n w)
  apply le_antisymm
  · refine le_iInf fun m => ?_
    refine (iInf_le (fun k => C k w) m).trans ?_
    rw [← hw m]
    refine iSup_le fun n => ?_
    refine (sInf_le_sInf ?_).trans (le_iSup (fun k => U m k w) n)
    rintro u ⟨r, hr, hB', rfl⟩
    exact ⟨r, ⟨hr.le, hB'⟩, rfl⟩
  · refine le_iInf fun m => ?_
    have ha : a (m + 1) < a m := by
      dsimp [a]
      have hh : (m : NNReal) + 1 < ((m + 1 : ℕ) : NNReal) + 1 := by
        push_cast
        linarith
      exact one_div_lt_one_div_of_lt (by positivity) hh
    refine (iInf_le (fun k => ⨆ n, U k n w) (m + 1)).trans ?_
    rw [← hw m]
    refine iSup_le fun n => ?_
    refine (sInf_le_sInf ?_).trans (le_iSup (fun k => V m k w) n)
    rintro u ⟨r, ⟨hr, hB'⟩, rfl⟩
    exact ⟨r, ha.trans_le hr, hB', rfl⟩
