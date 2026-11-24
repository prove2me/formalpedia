-- Prove2me | solution 1 for Kyprianou.Ch03.rawNaturalEventAETransferV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T14:45:19.27792+00:00
-- url     : https://prove2.me/submissions/ad12e281-92cf-46bc-954d-0fb5c41d63c9

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch03_CompletedNaturalFiltration
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X Y : NNReal → Omega → ℝ) (hEq : ∀ᵐ w ∂P, ∀ t, Y t w = X t w)
    (s : NNReal) (A : Set Omega) (hA : MeasurableSet[PerfCorrMSQ.natFiltr X s] A) :
    ∃ B : Set Omega, MeasurableSet[PerfCorrMSQ.natFiltr Y s] B ∧ A =ᵐ[P] B := by
  classical
  let V (Z : NNReal → Omega → ℝ) (w : Omega) (u : {u : NNReal // u ≤ s}) :=
    Z u.val w
  have he (Z : NNReal → Omega → ℝ) :
      PerfCorrMSQ.natFiltr Z s = MeasurableSpace.comap (V Z) inferInstance := by
    change (⨆ u : NNReal, ⨆ (_ : u ≤ s), MeasurableSpace.comap (Z u) inferInstance) = _
    apply le_antisymm
    · refine iSup_le fun u => iSup_le fun hu => ?_
      exact ((measurable_pi_apply ⟨u, hu⟩).comp (comap_measurable (V Z))).comap_le
    · letI : MeasurableSpace Omega := PerfCorrMSQ.natFiltr Z s
      apply Measurable.comap_le
      apply measurable_pi_iff.mpr
      intro u
      exact (comap_measurable (Z u.val)).mono (le_iSup₂_of_le u.val u.property le_rfl) le_rfl
  rw [he X] at hA
  obtain ⟨C, hC, rfl⟩ := hA
  refine ⟨(V Y) ⁻¹' C, ?_, ?_⟩
  · rw [he Y]
    exact (comap_measurable (V Y)) hC
  · filter_upwards [hEq] with w hw
    have h : V X w = V Y w := funext fun u => (hw u.val).symm
    change (V X w ∈ C) = (V Y w ∈ C)
    rw [h]
