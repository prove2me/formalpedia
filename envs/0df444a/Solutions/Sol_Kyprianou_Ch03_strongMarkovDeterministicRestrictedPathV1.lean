-- Prove2me | solution 1 for Kyprianou.Ch03.strongMarkovDeterministicRestrictedPathV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T07:32:00.702873+00:00
-- url     : https://prove2.me/submissions/e1af941e-c8c4-4444-8a63-bcc5a0271514

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch03_CompletedNaturalFiltration
import Theorems.Thm_Kyprianou_Ch03_strongMarkovCompletedIncrementFactorV1
import Theorems.Thm_Kyprianou_Ch03_strongMarkovDeterministicRestrictedFDDV1
import Theorems.Thm_AvramDividend_Classical_scaled_piPathMeasure_eq_of_finite_pushforwards
open MeasureTheory ProbabilityTheory Filter
open Kyprianou.Ch03
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (X : NNReal → Omega → Real)
    (hX : ProbabilityTheory.IsLevyProcess X P)
    (hNatural : IsCompletedNaturalFiltration P X F) :
    ∀ (s : NNReal) (B : Set Omega), MeasurableSet[F s] B →
      Measure.map (fun omega u => X (s + u) omega - X s omega) (P.restrict B) =
        P B • Measure.map (fun omega u => X u omega) P := by
  classical
  have hAdapt : ∀ t : NNReal, Measurable[F t] (X t) := by
    intro t
    apply (comap_measurable (X t)).mono _ le_rfl
    rw [hNatural t]
    exact le_sup_of_le_left (le_iSup₂_of_le t le_rfl le_rfl)
  have hMeas : ∀ t : NNReal, Measurable (X t) :=
    fun t => (hAdapt t).mono (F.le t) le_rfl
  intro s B hB
  let Y : Omega → (NNReal → Real) := fun w u => X (s + u) w - X s w
  let Z : Omega → (NNReal → Real) := fun w u => X u w
  have hY : Measurable Y := measurable_pi_iff.mpr (fun u => (hMeas _).sub (hMeas _))
  have hZ : Measurable Z := measurable_pi_iff.mpr hMeas
  apply AvramDividend.Classical.scaled_piPathMeasure_eq_of_finite_pushforwards
    Y Z hY hZ (P B) (measure_ne_top _ _)
  exact strongMarkovDeterministicRestrictedFDDV1 P F X hX hAdapt
    (strongMarkovCompletedIncrementFactorV1 P F X hX hNatural) s B hB
