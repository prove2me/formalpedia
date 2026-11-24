-- Prove2me | solution 1 for Kyprianou.Ch03.rawNaturalDeterministicRestrictedPathV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T13:21:13.355993+00:00
-- url     : https://prove2.me/submissions/136a1226-fa36-4ec5-978b-5e72768811a0

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch03_CompletedNaturalFiltration
import Theorems.Thm_Kyprianou_Ch01_levyIncrement_indep_naturalSigma
import Theorems.Thm_Kyprianou_Ch01_naturalSigma_eq_natFiltr
import Theorems.Thm_Kyprianou_Ch03_strongMarkovDeterministicRestrictedFDDV1
import Theorems.Thm_AvramDividend_Classical_scaled_piPathMeasure_eq_of_finite_pushforwards
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X : NNReal → Omega → ℝ) (hX : IsLevyProcess X P)
    (hMeas : ∀ t, Measurable (X t))
    (s : NNReal) (A : Set Omega) (hA : MeasurableSet[PerfCorrMSQ.natFiltr X s] A) :
    Measure.map (fun (w : Omega) (u : NNReal) => X (s + u) w - X s w) (P.restrict A) =
      P A • Measure.map (fun (w : Omega) (u : NNReal) => X u w) P := by
  classical
  let F := Filtration.natural X (fun t => (hMeas t).stronglyMeasurable)
  have hF (t : NNReal) : F t = PerfCorrMSQ.natFiltr X t := rfl
  have hAdapt (t : NNReal) : Measurable[F t] (X t) := by
    rw [hF]
    exact (comap_measurable (X t)).mono (le_iSup₂_of_le t le_rfl le_rfl) le_rfl
  have hOne (r q : NNReal) (hrq : r ≤ q) (B : Set Omega) (hB : MeasurableSet[F r] B)
      (C : Set ℝ) (hC : MeasurableSet C) :
      P (B ∩ {w | X q w - X r w ∈ C}) =
        P B * P {w | X q w - X r w ∈ C} := by
    have hi := (Kyprianou.Ch01.levyIncrement_indep_naturalSigma P X hX hMeas r q hrq).symm
    rw [Kyprianou.Ch01.naturalSigma_eq_natFiltr, ← hF] at hi
    exact (Indep_iff (F r) _ P).mp hi B _ hB ((comap_measurable _) hC)
  let U : Omega → (NNReal → ℝ) := fun w u => X (s + u) w - X s w
  let V : Omega → (NNReal → ℝ) := fun w u => X u w
  have hU : Measurable U := measurable_pi_iff.mpr fun u => (hMeas _).sub (hMeas _)
  have hV : Measurable V := measurable_pi_iff.mpr hMeas
  apply AvramDividend.Classical.scaled_piPathMeasure_eq_of_finite_pushforwards
    U V hU hV (P A) (measure_ne_top _ _)
  exact Kyprianou.Ch03.strongMarkovDeterministicRestrictedFDDV1 P F X hX hAdapt hOne s A
    (by rw [hF]; exact hA)
