-- Prove2me | solution 1 for Kyprianou.Ch05.killedPotential_laplaceTransform
-- status  : ACCEPTED   (prove)
-- author  : @pageman
-- created : 2026-11-26T03:21:36.204204+00:00
-- url     : https://prove2.me/submissions/b7ce632e-f134-4504-bfce-0563d82fdca5

import Mathlib
import Mathlib.MeasureTheory.Group.Convolution
import Definitions.Def_Kyprianou_Ch03_IsSubordinator
import Definitions.Def_Kyprianou_Ch03_EntryAndHittingTimes
import Definitions.Def_Kyprianou_Ch05_RenewalMeasure
import Definitions.Def_Kyprianou_Ch05_KilledSubordinatorPotential
import Theorems.Thm_Kyprianou_Ch05_killedPotential_lintegral_formula
import Theorems.Thm_Kyprianou_Ch05_killedPotential_resolvent_integral
open MeasureTheory Filter ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (Y : NNReal → Omega → Real)
    (death : Omega → WithTop NNReal)
    (eta d : Real) (Pi : Measure Real) (Phi : Real → Real)
    (hKilled : Kyprianou.Ch05.IsKilledSubordinator P Y death eta)
    (hTriplet : Kyprianou.Ch05.IsKilledLaplaceTriplet eta d Pi Phi)
    (hLaplaceLaw : ∀ (t : NNReal) (theta : Real), 0 ≤ theta →
      (∫ omega, Real.exp (-theta * Y t omega) ∂P) =
        Real.exp (-(t : Real) * (Phi theta - eta)))
    (U : Real → Measure Real)
    (hPotential : Kyprianou.Ch05.IsKilledPotentialFamily P Y death U) :
  ∀ q : Real, 0 ≤ q → ∀ theta : Real, 0 ≤ theta →
      (∫⁻ x : Real, ENNReal.ofReal (Real.exp (-theta * x)) ∂(U q)) =
        (ENNReal.ofReal (q + Phi theta))⁻¹ := by
  intro q hq theta htheta
  rw [Kyprianou.Ch05.killedPotential_lintegral_formula P Y death eta d Pi Phi
    hKilled hTriplet hLaplaceLaw U hPotential q hq
    (fun x : Real => ENNReal.ofReal (Real.exp (-theta * x))) (by fun_prop)]
  exact Kyprianou.Ch05.killedPotential_resolvent_integral P Y death eta d Pi Phi
    hKilled hTriplet hLaplaceLaw U hPotential q hq theta htheta
