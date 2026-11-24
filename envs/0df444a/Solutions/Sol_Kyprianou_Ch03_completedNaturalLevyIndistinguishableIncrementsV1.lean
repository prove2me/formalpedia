-- Prove2me | solution 1 for Kyprianou.Ch03.completedNaturalLevyIndistinguishableIncrementsV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T19:09:40.3188+00:00
-- url     : https://prove2.me/submissions/ea0603e4-804f-41a8-8991-5523064a75d1

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch03_CompletedNaturalFiltration
import Theorems.Thm_Kyprianou_Ch03_completedNaturalMeasurableAEModV1
import Theorems.Thm_Kyprianou_Ch03_strongMarkovCompletedIncrementFactorV1
import Theorems.Thm_AvramDividend_Classical_avram_a57_raw_sigma_independence_preserved_by_conull_source_equality_20261114
open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
set_option autoImplicit false
theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X : NNReal → Omega → ℝ)
    (hX : ProbabilityTheory.IsLevyProcess X P)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (hNatural : Kyprianou.Ch03.IsCompletedNaturalFiltration P X F)
    (Y : NNReal → Omega → ℝ)
    (hY : ∀ᵐ omega ∂P, ∀ t : NNReal, Y t omega = X t omega)
    (hMeas : ∀ t, Measurable (Y t)) :
    Adapted F Y ∧
      (∀ s t, s ≤ t →
        Indep (MeasurableSpace.comap (fun omega => Y t omega - Y s omega)
          inferInstance) (F s) P) ∧
      (∀ s t, s ≤ t →
        IdentDistrib (fun omega => Y t omega - Y s omega) (Y (t - s)) P P) := by
  have hInc (s t : NNReal) :
      (fun w => Y t w - Y s w) =ᵐ[P] (fun w => X t w - X s w) :=
    hY.mono (fun _ h => by simp only [h])
  refine ⟨?_, ?_, ?_⟩
  · intro t C hC
    have hx : Measurable[F t] (X t) := by
      apply (comap_measurable (X t)).mono _ le_rfl
      rw [hNatural t]
      exact le_sup_of_le_left (le_iSup₂_of_le t le_rfl le_rfl)
    exact Kyprianou.Ch03.completedNaturalMeasurableAEModV1 P F X hNatural t
      (Y t ⁻¹' C) (X t ⁻¹' C) (hx hC)
      (hY.mono (fun w hw => by simp only [mem_preimage, hw t]))
  · intro s t hst
    let g : Omega → ℝ := fun w => X t w - X s w
    have hi : Indep (MeasurableSpace.comap g inferInstance) (F s) P := by
      rw [Indep_iff]
      intro B A hB hA
      obtain ⟨C, hC, rfl⟩ := hB
      rw [inter_comm, mul_comm]
      exact Kyprianou.Ch03.strongMarkovCompletedIncrementFactorV1 P F X hX hNatural
        s t hst A hA C hC
    exact AvramDividend.Classical.avram_a57_raw_sigma_independence_preserved_by_conull_source_equality_20261114
      (F s) g (fun w => Y t w - Y s w) (hInc s t).symm hi
  · intro s t hst
    have h := hX.stationary_increments s (t - s)
    rw [add_tsub_cancel_of_le hst] at h
    change IdentDistrib (fun w => X t w - X s w)
      (fun w => X (t - s) w - X 0 w) P P at h
    have hz : (fun w => X (t - s) w - X 0 w) = X (t - s) := by
      funext w
      rw [congrFun hX.start_zero w, sub_zero]
    rw [hz] at h
    exact (IdentDistrib.of_ae_eq ((hMeas t).sub (hMeas s)).aemeasurable (hInc s t)).trans
      (h.trans (IdentDistrib.of_ae_eq (hMeas (t - s)).aemeasurable
        (hY.mono (fun _ hw => hw (t - s)))).symm)
