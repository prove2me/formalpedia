-- Prove2me | solution 1 for Kyprianou.Ch03.completedStoppingInfSupAEEqV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T12:16:50.908293+00:00
-- url     : https://prove2.me/submissions/5178819b-d525-4a81-af1e-bde8ea5462de

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
    (T : Omega → WithTop NNReal)
    (U : ℕ → ℕ → Omega → WithTop NNReal)
    (hRC : F.IsRightContinuous)
    (hU : ∀ m n, IsStoppingTime F (U m n))
    (hEq : T =ᵐ[P] (fun w => ⨅ m : ℕ, ⨆ n : ℕ, U m n w)) :
    IsStoppingTime F T := by
  letI : F.IsRightContinuous := hRC
  have hsup (m : ℕ) : IsStoppingTime F (fun w => ⨆ n : ℕ, U m n w) := by
    intro t
    have he : {w : Omega | (⨆ n : ℕ, U m n w) ≤ (t : WithTop NNReal)} =
        ⋂ n : ℕ, {w : Omega | U m n w ≤ (t : WithTop NNReal)} := by
      ext w
      simp only [Set.mem_setOf_eq, Set.mem_iInter]
      exact iSup_le_iff
    rw [he]
    exact MeasurableSet.iInter (fun n => hU m n t)
  have hinf : IsStoppingTime F (fun w => ⨅ m : ℕ, ⨆ n : ℕ, U m n w) := by
    first
    | exact IsStoppingTime.iInf hsup
    | exact IsStoppingTime.iInf F hsup
  change ∀ᵐ w ∂P, T w = (⨅ m : ℕ, ⨆ n : ℕ, U m n w) at hEq
  rw [ae_iff] at hEq
  obtain ⟨N, hNsub, hNm, hN0⟩ := exists_measurable_superset_of_null hEq
  intro t
  let A := {w : Omega | T w ≤ (t : WithTop NNReal)}
  let D := {w : Omega | (⨅ m : ℕ, ⨆ n : ℕ, U m n w) ≤ (t : WithTop NNReal)}
  have hnull (C : Set Omega) (hC : C ⊆ N) : MeasurableSet[F t] C := by
    rw [hNatural t]
    exact (le_sup_right : _ ≤ PerfCorrMSQ.natFiltr X t ⊔ _) C
      (MeasurableSpace.measurableSet_generateFrom ⟨N, hNm, hN0, hC⟩)
  have he : A = (D \ N) ∪ (A ∩ N) := by
    ext w
    by_cases hw : w ∈ N
    · simp [A, D, hw]
    · have hh : T w = (⨅ m : ℕ, ⨆ n : ℕ, U m n w) := by
        by_contra hn
        exact hw (hNsub hn)
      simp [A, D, hw, hh]
  change MeasurableSet[F t] A
  rw [he]
  exact ((hinf t).diff (hnull N subset_rfl)).union (hnull _ Set.inter_subset_right)
