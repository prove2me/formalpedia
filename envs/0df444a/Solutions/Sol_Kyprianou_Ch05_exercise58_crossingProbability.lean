-- Prove2me | solution 1 for Kyprianou.Ch05.exercise58_crossingProbability
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T21:56:46.945397+00:00
-- url     : https://prove2.me/submissions/515d12d5-bfd1-43dc-af52-4bb3b3defe95

import Mathlib
import Theorems.Thm_Kyprianou_Ch05_monotonePassageClockNonnegativeV1
import Theorems.Thm_Kyprianou_Ch05_killedPassageProbabilityClockV1
import Theorems.Thm_Kyprianou_Ch05_killedPotentialTailClockV1
import Definitions.Def_Kyprianou_Ch05_KilledSubordinatorPotential
import Definitions.Def_Kyprianou_Ch05_FirstPassageObservables
import Definitions.Def_Kyprianou_Ch05_RenewalMeasure
import Definitions.Def_Kyprianou_Ch05_TailRatioClassL
open MeasureTheory Filter ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false

open Set Topology Kyprianou.Ch05
open scoped Classical Topology
open Kyprianou.Ch05

/-- Exercise 5.8, full five parts including the alpha=0 escape case. -/
theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (Y : NNReal → Omega → Real)
    (death : Omega → WithTop NNReal)
    (eta d alpha : Real) (Pi : Measure Real)
    (Phi : Real → Real) (U : Real → Measure Real)
    (hEta : 0 < eta)
    (hKilled : IsKilledSubordinator P Y death eta)
    (hTriplet : IsKilledLaplaceTriplet eta d Pi Phi)
    (hLaplaceLaw : ∀ (t : NNReal) (theta : Real), 0 ≤ theta →
      (∫ omega, Real.exp (-theta * Y t omega) ∂P) =
         Real.exp (-(t : Real) * (Phi theta-eta)))
    (hPotential : IsKilledPotentialFamily P Y death U)
    (hClassL : IsTailRatioClassL (U 0) alpha)
    (hExtMoment : IntegrableOn
      (fun z : Real => Real.exp (alpha*z)-1) (Set.Ioi 0) Pi)
    (hExtendedPhi : Phi (-alpha) = eta-d*alpha +
      ∫ z in Set.Ioi (0 : Real),
         (1-Real.exp (alpha*z)) ∂Pi)
 :
  (∀ x : Real, 0 ≤ x →
    (P {omega : Omega | PassageFinite Y death x omega}).toReal =
       eta*(U 0 (Set.Ioi x)).toReal)
 := by
  classical
  intro x hx
  obtain ⟨T,hTm,hT⟩ := monotonePassageClockNonnegativeV1 x hx
  rw [killedPassageProbabilityClockV1 P Y death eta hKilled x T hTm hT,
    killedPotentialTailClockV1 P Y death eta hKilled d Pi Phi hTriplet
      hLaplaceLaw U hPotential hEta x T hTm hT hx]
  rw [← ENNReal.toReal_ofReal hEta.le,← ENNReal.toReal_mul]
  congr 1
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply lintegral_congr
  intro w
  by_cases ht : T (fun t => Y t w) = ⊤
  · simp [ht]
  · simp only [ht,ne_eq,not_false_eq_true,if_true]
    rw [← ENNReal.ofReal_mul hEta.le]
    congr 1
    rw [ENNReal.toReal_ofReal hEta.le]
    field_simp

