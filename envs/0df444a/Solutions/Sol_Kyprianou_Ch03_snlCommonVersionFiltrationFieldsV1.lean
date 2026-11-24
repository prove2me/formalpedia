-- Prove2me | solution 1 for Kyprianou.Ch03.snlCommonVersionFiltrationFieldsV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T19:02:41.091119+00:00
-- url     : https://prove2.me/submissions/1a8b1acc-2e4d-4f6b-8fb3-14fc18d120ab

import Theorems.Thm_Kyprianou_Ch03_completedNaturalMeasurableAEModV1
import Theorems.Thm_Kyprianou_Ch03_strongMarkovCompletedIncrementFactorV1
import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_Kyprianou_Ch03_CompletedNaturalFiltration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false

open Set
open scoped Topology


theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (X : NNReal → Omega → ℝ)
    (hX : ProbabilityTheory.IsLevyProcess X P)
    (hNatural : Kyprianou.Ch03.IsCompletedNaturalFiltration P X F)
    (Y : NNReal → Omega → ℝ)
    (hEq : ∀ᵐ w ∂P, ∀ t, Y t w = X t w)
    (hMeas : ∀ t, Measurable (Y t)) :
    Adapted F Y ∧
      (∀ s t : NNReal, s ≤ t →
        Indep (MeasurableSpace.comap (fun w => Y t w - Y s w) inferInstance) (F s) P) ∧
      (∀ s t : NNReal, s ≤ t →
        IdentDistrib (fun w => Y t w - Y s w) (Y (t - s)) P P) := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · intro t
    have hXt : Measurable[F t] (X t) := by
      apply (comap_measurable (X t)).mono _ le_rfl
      rw [hNatural t]
      exact le_sup_of_le_left (le_iSup₂_of_le t le_rfl le_rfl)
    intro C hC
    apply Kyprianou.Ch03.completedNaturalMeasurableAEModV1 P F X hNatural t
      (Y t ⁻¹' C) (X t ⁻¹' C) (hXt hC)
    filter_upwards [hEq] with w hw
    change Y t w ∈ C ↔ X t w ∈ C
    rw [hw t]
  · intro s t hst
    apply (Indep_iff _ _ P).mpr
    intro B A hB hA
    obtain ⟨C, hC, rfl⟩ := hB
    have he : ∀ᵐ w ∂P, Y t w - Y s w = X t w - X s w := by
      filter_upwards [hEq] with w hw
      rw [hw t, hw s]
    have hpre : ({w | Y t w - Y s w ∈ C} : Set Omega) =ᵐ[P]
        ({w | X t w - X s w ∈ C} : Set Omega) := by
      filter_upwards [he] with w hw
      change (Y t w - Y s w ∈ C) = (X t w - X s w ∈ C)
      rw [hw]
    have hinter : (({w | Y t w - Y s w ∈ C} : Set Omega) ∩ A : Set Omega) =ᵐ[P]
        (({w | X t w - X s w ∈ C} : Set Omega) ∩ A : Set Omega) := by
      filter_upwards [he] with w hw
      change (Y t w - Y s w ∈ C ∧ w ∈ A) = (X t w - X s w ∈ C ∧ w ∈ A)
      rw [hw]
    change P ({w | Y t w - Y s w ∈ C} ∩ A) =
      P {w | Y t w - Y s w ∈ C} * P A
    rw [measure_congr hinter, measure_congr hpre, Set.inter_comm, mul_comm]
    exact Kyprianou.Ch03.strongMarkovCompletedIncrementFactorV1 P F X hX hNatural s t hst A hA C hC
  · intro s t hst
    have hi (a b : NNReal) : IdentDistrib (ProbabilityTheory.increment Y a b)
        (ProbabilityTheory.increment X a b) P P := by
      apply IdentDistrib.of_ae_eq ((hMeas b).sub (hMeas a)).aemeasurable
      filter_upwards [hEq] with w hw
      simp [ProbabilityTheory.increment, hw]
    have ht := ((hi s (s + (t - s))).trans (hX.stationary_increments s (t - s))).trans
      (hi 0 (t - s)).symm
    have hz : IdentDistrib (ProbabilityTheory.increment Y 0 (t - s)) (Y (t - s)) P P := by
      apply IdentDistrib.of_ae_eq ((hMeas _).sub (hMeas 0)).aemeasurable
      filter_upwards [hEq] with w hw
      simp [ProbabilityTheory.increment, hw, hX.start_zero]
    change IdentDistrib (ProbabilityTheory.increment Y s t) (Y (t - s)) P P
    simpa only [add_tsub_cancel_of_le hst] using ht.trans hz
