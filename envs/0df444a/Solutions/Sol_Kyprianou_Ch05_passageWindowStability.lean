-- Prove2me | solution 1 for Kyprianou.Ch05.passageWindowStability
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Jonats Zerep
-- created : 2026-11-27T03:01:05.613374+00:00
-- url     : https://prove2.me/submissions/d5c5a65f-9ba7-4c7d-b34f-2709e4000f77
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_Kyprianou_Ch05_RegularVariation
import Definitions.Def_Kyprianou_Ch05_RenewalMeasure
import Definitions.Def_Kyprianou_Ch05_KilledSubordinatorPotential
import Definitions.Def_Kyprianou_Ch05_FirstPassageObservables
import Definitions.Def_Kyprianou_Ch05_WeakPassageObservables
import Theorems.Thm_Kyprianou_Ch05_passageTestStability
import Theorems.Thm_Kyprianou_Ch05_jumpTruncatedStability
open MeasureTheory Filter ProbabilityTheory
open scoped NNReal ENNReal
open Kyprianou.Ch05
set_option autoImplicit false

theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (Y Yleft : NNReal → Omega → Real)
    (death : Omega → WithTop NNReal)
    (d : Real) (Pi : Measure Real) (Phi : Real → Real)
    (hKilled : IsKilledSubordinator P Y death 0)
    (hTriplet : IsKilledLaplaceTriplet 0 d Pi Phi)
    (hLaplaceLaw : ∀ (t : NNReal) (theta : Real), 0 ≤ theta →
      (∫ omega, Real.exp (-theta * Y t omega) ∂P) =
        Real.exp (-(t : Real) * Phi theta))
    (hLeft : IsLeftLimitVersion P Y Yleft)
    (U : Real → Measure Real)
    (hPotential : IsKilledPotentialFamily P Y death U)
    (hFiniteMean : Integrable (Y (1 : NNReal)) P)
    (hPositiveMean : 0 < ∫ omega, Y 1 omega ∂P)
    (hNonLattice : NonLatticeMeasure (U 0)) :
  ∀ f g : Real × Real → Real, IsBoundedContinuousTest f → IsBoundedContinuousTest g →
    f (0, 0) = 0 → g (0, 0) = 0 → ∀ η : Real, 0 < η →
    (∀ z : Real × Real, |f z - g z| ≤ η) → ∀ᶠ x : Real in atTop,
      |passageTestExpectation P Y Yleft death x f - passageTestExpectation P Y Yleft death x g| ≤ η ∧
      |(1 / (∫ omega, Y 1 omega ∂P)) * (∫ y in Set.Icc (0 : Real) x, ∫ z in Set.Ioi y, f (z - y, y) ∂Pi ∂volume) - (1 / (∫ omega, Y 1 omega ∂P)) * (∫ y in Set.Icc (0 : Real) x, ∫ z in Set.Ioi y, g (z - y, y) ∂Pi ∂volume)| ≤ η * ((∫ y in Set.Ici (0 : Real), (Pi (Set.Ioi y)).toReal ∂volume) / (∫ omega, Y 1 omega ∂P)) := by
  intro f g hf hg hf0 hg0 η hη hsup
  refine Filter.Eventually.of_forall fun x => ⟨?_, ?_⟩
  · exact Kyprianou.Ch05.passageTestStability
      P Y Yleft death d Pi Phi hKilled hTriplet hLaplaceLaw hLeft U hPotential
      hFiniteMean hPositiveMean hNonLattice f g hf hg hf0 hg0 η hη hsup x
  · exact Kyprianou.Ch05.jumpTruncatedStability
      P Y Yleft death d Pi Phi hKilled hTriplet hLaplaceLaw hLeft U hPotential
      hFiniteMean hPositiveMean hNonLattice f g hf hg hf0 hg0 η hη hsup x
