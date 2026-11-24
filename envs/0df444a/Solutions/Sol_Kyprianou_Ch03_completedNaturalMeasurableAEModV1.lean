-- Prove2me | solution 1 for Kyprianou.Ch03.completedNaturalMeasurableAEModV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T12:31:15.953282+00:00
-- url     : https://prove2.me/submissions/41e9f818-f67c-44de-a342-306980a47494

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch03_CompletedNaturalFiltration
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (X : NNReal → Omega → ℝ)
    (hNatural : Kyprianou.Ch03.IsCompletedNaturalFiltration P X F)
    (s : NNReal) (A U : Set Omega) (hU : MeasurableSet[F s] U)
    (hEq : ∀ᵐ w ∂P, w ∈ A ↔ w ∈ U) : MeasurableSet[F s] A := by
  rw [ae_iff] at hEq
  obtain ⟨N, hNsub, hNm, hN0⟩ := exists_measurable_superset_of_null hEq
  have hnull (C : Set Omega) (hC : C ⊆ N) : MeasurableSet[F s] C := by
    rw [hNatural s]
    exact (le_sup_right : _ ≤ PerfCorrMSQ.natFiltr X s ⊔ _) C
      (MeasurableSpace.measurableSet_generateFrom ⟨N, hNm, hN0, hC⟩)
  have he : A = (U \ N) ∪ (A ∩ N) := by
    ext w
    by_cases hw : w ∈ N
    · simp [hw]
    · have h : w ∈ A ↔ w ∈ U := by
        by_contra hn
        exact hw (hNsub hn)
      simp [hw, h]
  rw [he]
  exact (hU.diff (hnull N subset_rfl)).union (hnull _ Set.inter_subset_right)
