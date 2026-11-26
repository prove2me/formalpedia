-- Prove2me | solution 1 for Kyprianou.Ch05.killedSubordinator_charFun_re_eq_exp_mul_cos
-- status  : ACCEPTED   (prove)
-- author  : @pageman
-- created : 2026-11-26T12:13:19.799517+00:00
-- url     : https://prove2.me/submissions/a98b7a73-585d-483a-b3f5-2a68a218ac86

import Mathlib
import Mathlib.MeasureTheory.Group.Convolution
import Definitions.Def_Kyprianou_Ch03_IsSubordinator
import Definitions.Def_Kyprianou_Ch03_EntryAndHittingTimes
import Definitions.Def_Kyprianou_Ch05_RenewalMeasure
import Definitions.Def_Kyprianou_Ch05_KilledSubordinatorPotential
import Theorems.Thm_Kyprianou_Ch05_killedSubordinator_charFun_eq_exp_mul
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
  ∀ (t : NNReal) (u : Real),
    (MeasureTheory.charFun (P.map (Y t)) u).re =
       Real.exp (-(t : Real) * (∫⁻ x in Set.Ioi (0 : Real), ENNReal.ofReal (1 - Real.cos (u * x)) ∂Pi).toReal) * Real.cos ((t : Real) * (∫ x in Set.Ioi (0 : Real), Real.sin (u * x) ∂Pi + d * u)) := by
  intro t u
  have h := Kyprianou.Ch05.killedSubordinator_charFun_eq_exp_mul
    P Y death eta d Pi Phi hKilled hTriplet hLaplaceLaw U hPotential t u
  rw [h, Complex.exp_re]
  simp
