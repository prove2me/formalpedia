-- Prove2me | solution 1 for Kyprianou.Ch03.quasiLeftContinuousAlongStoppingTimes
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T14:58:17.506255+00:00
-- url     : https://prove2.me/submissions/99482fe4-4239-4118-a5da-8e72a29e7231

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch03_CompletedNaturalFiltration
import Theorems.Thm_Kyprianou_Ch03_quasiLeft_stoppingSequenceLimit
import Theorems.Thm_Kyprianou_Ch03_quasiLeft_strictlyEarlierLeftLimit
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch03

theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (X : NNReal -> Omega -> Real)
    (hX : ProbabilityTheory.IsLevyProcess X P)
    (hNatural : IsCompletedNaturalFiltration P X F)
    (T : Omega -> WithTop NNReal)
    (Tn : Nat -> Omega -> WithTop NNReal)
    (timeT : Omega -> NNReal) (timeTn : Nat -> Omega -> NNReal)
    (hTimeT : forall omega, T omega != ⊤ ->
      T omega = (timeT omega : WithTop NNReal))
    (hTimeTn : forall n omega, Tn n omega != ⊤ ->
      Tn n omega = (timeTn n omega : WithTop NNReal))
    (hT : IsStoppingTime F T)
    (hTn : forall n, IsStoppingTime F (Tn n))
    (hIncreasing : ∀ᵐ omega : Omega ∂ P,
      Monotone (fun n => Tn n omega))
    (hLimit : ∀ᵐ omega : Omega ∂ P,
      Tendsto (fun n => Tn n omega) atTop (nhds (T omega))) :
    (∀ᵐ omega : Omega ∂ P, T omega != ⊤ ->
      Tendsto (fun n => X (timeTn n omega) omega)
        atTop (nhds (X (timeT omega) omega))) ∧
    (∀ᵐ omega : Omega ∂ P, T omega != ⊤ ->
      (forall n, Tn n omega < T omega) ->
      Function.leftLim (fun s : NNReal => X s omega) (timeT omega) =
        X (timeT omega) omega) := by
  exact ⟨
    Kyprianou.Ch03.quasiLeft_stoppingSequenceLimit P F X hX hNatural T Tn timeT timeTn hTimeT hTimeTn hT hTn hIncreasing hLimit,
    Kyprianou.Ch03.quasiLeft_strictlyEarlierLeftLimit P F X hX hNatural T Tn timeT timeTn hTimeT hTimeTn hT hTn hIncreasing hLimit
  ⟩
