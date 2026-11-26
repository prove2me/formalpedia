-- Prove2me | solution 1 for Kyprianou.Ch05.exercise54CorrelatedBivariateQuadrupleLaw
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Cloud 
-- created : 2026-11-26T03:16:23.528013+00:00
-- url     : https://prove2.me/submissions/29a4cc94-f198-44d0-b114-dfc535832938
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_Kyprianou_Ch05_exercise54BivariateCompensationIntegral
import Theorems.Thm_Kyprianou_Ch05_exercise54QuadrupleKernelUnfold
import Mathlib
import Definitions.Def_Kyprianou_Ch03_IsSubordinator
import Definitions.Def_Kyprianou_Ch05_KilledSubordinatorPotential
import Definitions.Def_Kyprianou_Ch05_FirstPassageObservables
import Definitions.Def_Kyprianou_Ch05_BivariateKilledSubordinator
open MeasureTheory Filter ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch05

theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X Y Xleft Yleft : NNReal → Omega → Real)
    (death : Omega → WithTop NNReal)
    (eta dX dY : Real)
    (Pi U : Measure (Real × Real))
    (hBivariate : IsKilledBivariateSubordinator P X Y death eta dX dY Pi)
    (hPotential : IsBivariateKilledPotential P X Y death U)
    (hLeftX : IsLeftLimitVersion P X Xleft)
    (hLeftY : IsLeftLimitVersion P Y Yleft) :
  ∀ x : Real, 0 < x →
    ∀ T S B A : Set Real,
      MeasurableSet T → MeasurableSet S →
      MeasurableSet B → MeasurableSet A →
      T ⊆ Set.Ici (0 : Real) → S ⊆ Set.Ici (0 : Real) →
      B ⊆ Set.Icc (0 : Real) x → A ⊆ Set.Ioi (0 : Real) →
      P {omega : Omega |
        PassageFinite Y death x omega ∧
        (X (passageFiniteTime Y death x omega) omega -
          Xleft (passageFiniteTime Y death x omega) omega) ∈ T ∧
        Xleft (passageFiniteTime Y death x omega) omega ∈ S ∧
        (x - Yleft (passageFiniteTime Y death x omega) omega) ∈ B ∧
        (Y (passageFiniteTime Y death x omega) omega-x) ∈ A} =
       bivariateQuadrupleKernel U Pi x T S B A
 := by
  intro x hx T S B A hT hS hB hA hTsub hSsub hBsub hAsub
  rw [exercise54QuadrupleKernelUnfold]
  exact exercise54BivariateCompensationIntegral P X Y Xleft Yleft death eta dX dY Pi U
    hBivariate hPotential hLeftX hLeftY x hx T S B A hT hS hB hA hTsub hSsub hBsub hAsub
