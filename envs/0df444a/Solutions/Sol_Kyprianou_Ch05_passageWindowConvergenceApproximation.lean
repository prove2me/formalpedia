-- Prove2me | solution 1 for Kyprianou.Ch05.passageWindowConvergenceApproximation
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Jonats Zerep
-- created : 2026-11-27T02:54:08.753798+00:00
-- url     : https://prove2.me/submissions/dca7aada-eff2-4e21-a3e1-51f62bc5f201
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_Kyprianou_Ch05_RegularVariation
import Definitions.Def_Kyprianou_Ch05_RenewalMeasure
import Definitions.Def_Kyprianou_Ch05_KilledSubordinatorPotential
import Definitions.Def_Kyprianou_Ch05_FirstPassageObservables
import Definitions.Def_Kyprianou_Ch05_WeakPassageObservables
import Theorems.Thm_Kyprianou_Ch05_passageWindowLipschitzApproximation
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
    (hNonLattice : NonLatticeMeasure (U 0))
    (hLip : ∀ f : Real × Real → Real, IsBoundedContinuousTest f → f (0, 0) = 0 →
      (∃ C : Real, ∀ p q : Real × Real, |f p - f q| ≤ C * (|p.1 - q.1| + |p.2 - q.2|)) →
      ∀ ε : Real, 0 < ε → ∀ᶠ x : Real in atTop,
        |passageTestExpectation P Y Yleft death x f - (1 / (∫ omega, Y 1 omega ∂P)) * (∫ y in Set.Icc (0 : Real) x, ∫ z in Set.Ioi y, f (z - y, y) ∂Pi ∂volume)| ≤ ε) :
  ∀ f : Real × Real → Real, IsBoundedContinuousTest f → f (0, 0) = 0 →
    ∀ ε : Real, 0 < ε → ∀ᶠ x : Real in atTop,
      |passageTestExpectation P Y Yleft death x f - (1 / (∫ omega, Y 1 omega ∂P)) * (∫ y in Set.Icc (0 : Real) x, ∫ z in Set.Ioi y, f (z - y, y) ∂Pi ∂volume)| ≤ ε := by
  intro f hf hf0 ε hε
  obtain ⟨g, hg, hg0, hCg, hgclose⟩ := Kyprianou.Ch05.passageWindowLipschitzApproximation
    P Y Yleft death d Pi Phi hKilled hTriplet hLaplaceLaw hLeft U hPotential
    hFiniteMean hPositiveMean hNonLattice f hf hf0 (ε / 3) (by linarith)
  have h2 := hLip g hg hg0 hCg (ε / 3) (by linarith)
  filter_upwards [hgclose, h2] with x hx hx2
  obtain ⟨hx1, hx3⟩ := hx
  have h1' := abs_le.mp hx1
  have h2' := abs_le.mp hx2
  have h3' := abs_le.mp hx3
  rw [abs_le]
  constructor <;> linarith
