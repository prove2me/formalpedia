-- Prove2me | solution 1 for Kyprianou.Ch03.completedStoppingTimeIInfISupAEEqV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T12:02:15.455811+00:00
-- url     : https://prove2.me/submissions/c0a31603-06d5-4c7d-b2b4-3154d39e2d71

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch03_EntryAndHittingTimes
import Definitions.Def_Kyprianou_Ch03_CompletedNaturalFiltration
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (X : NNReal → Omega → Real) (hX : IsLevyProcess X P)
    (hNatural : Kyprianou.Ch03.IsCompletedNaturalFiltration P X F)
    (hRC : F.IsRightContinuous)
    (T : ℕ → ℕ → Omega → WithTop NNReal)
    (hT : ∀ j n, IsStoppingTime F (T j n))
    (S : Omega → WithTop NNReal)
    (hEq : ∀ᵐ w ∂P, S w = ⨅ j : ℕ, ⨆ n : ℕ, T j n w) :
    IsStoppingTime F S := by
  have hsup (j : ℕ) : IsStoppingTime F (fun w => ⨆ n : ℕ, T j n w) := by
    intro t
    have he : {w | (⨆ n : ℕ, T j n w) ≤ (t : WithTop NNReal)} =
        ⋂ n : ℕ, {w | T j n w ≤ (t : WithTop NNReal)} := by
      ext w
      simp only [Set.mem_setOf_eq, Set.mem_iInter, iSup_le_iff]
    rw [he]
    exact MeasurableSet.iInter fun n => hT j n t
  have hi : IsStoppingTime F (fun w => ⨅ j : ℕ, ⨆ n : ℕ, T j n w) := by
    letI := hRC
    exact IsStoppingTime.iInf hsup
  have hae := hEq
  rw [ae_iff] at hae
  obtain ⟨N, hNsub, hNm, hN0⟩ := exists_measurable_superset_of_null hae
  intro t
  let A := {w | S w ≤ (t : WithTop NNReal)}
  let B := {w | (⨅ j : ℕ, ⨆ n : ℕ, T j n w) ≤ (t : WithTop NNReal)}
  have hnull (C : Set Omega) (hC : C ⊆ N) : MeasurableSet[F t] C := by
    rw [hNatural t]
    exact (le_sup_right : _ ≤ PerfCorrMSQ.natFiltr X t ⊔ _) C
      (MeasurableSpace.measurableSet_generateFrom ⟨N, hNm, hN0, hC⟩)
  have he : A = (B \ N) ∪ (A ∩ N) := by
    ext w
    by_cases hw : w ∈ N
    · simp [hw]
    · have h : S w = ⨅ j : ℕ, ⨆ n : ℕ, T j n w := by
        by_contra hn
        exact hw (hNsub hn)
      simp [A, B, hw, h]
  change MeasurableSet[F t] A
  rw [he]
  exact ((hi t).diff (hnull N subset_rfl)).union (hnull _ Set.inter_subset_right)
