-- Prove2me | solution 1 for Kyprianou.Ch03.strongMarkovAtExtendedStoppingTime
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T07:12:46.657706+00:00
-- url     : https://prove2.me/submissions/0e627aea-5678-4e72-ad21-23158db96274

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch03_CompletedNaturalFiltration
import Theorems.Thm_Kyprianou_Ch03_strongMarkovDeterministicRestrictedPathV1
import Theorems.Thm_Kyprianou_Ch03_strongMarkovExtendedRestrictedPathV1
import Theorems.Thm_Kyprianou_Ch03_strongMarkovExtendedIndicatorAssemblyV1
open MeasureTheory ProbabilityTheory Filter Kyprianou.Ch03
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (X : NNReal -> Omega -> Real)
    (hX : ProbabilityTheory.IsLevyProcess X P)
    (hNatural : IsCompletedNaturalFiltration P X F)
    (tau : Omega -> WithTop NNReal)
    (hTau : IsStoppingTime F tau)
    (finiteTime : Omega -> NNReal)
    (hFiniteTime : forall omega, tau omega != ⊤ ->
      tau omega = (finiteTime omega : WithTop NNReal)) :
    forall A : Set Omega,
      (forall s : NNReal,
        MeasurableSet[F s]
          (Set.inter A {omega : Omega | tau omega <= (s : WithTop NNReal)})) ->
      Measure.map
        (fun omega : Omega =>
          (Set.indicator A (fun _ : Omega => (1 : Real)) omega,
           fun u : NNReal =>
             X (finiteTime omega + u) omega - X (finiteTime omega) omega))
        (P.restrict {omega : Omega | tau omega != ⊤}) =
      (Measure.map
        (Set.indicator A (fun _ : Omega => (1 : Real)))
        (P.restrict {omega : Omega | tau omega != ⊤})).prod
        (Measure.map (fun omega : Omega => fun u : NNReal => X u omega) P) := by
  have hDet := strongMarkovDeterministicRestrictedPathV1 P F X hX hNatural
  have hFinite' : ∀ omega, tau omega ≠ ⊤ →
      tau omega = (finiteTime omega : WithTop NNReal) := by
    intro omega h
    exact hFiniteTime omega (by simpa using h)
  have hSet : {omega : Omega | tau omega != ⊤} =
      {omega : Omega | tau omega ≠ ⊤} := by
    ext omega
    simp
  rw [hSet]
  obtain ⟨hY, hLaw⟩ := strongMarkovExtendedRestrictedPathV1
    P F X hX hNatural hDet tau hTau finiteTime hFinite'
  exact strongMarkovExtendedIndicatorAssemblyV1 P F tau hTau _ _ hY hLaw
