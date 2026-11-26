-- Prove2me | solution 1 for Kyprianou.Ch05.killedPotential_resolvent_integral
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @pageman
-- created : 2026-11-26T03:23:55.745796+00:00
-- url     : https://prove2.me/submissions/af7b43cc-c530-4ac2-b829-85b7b51791a5
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Mathlib.MeasureTheory.Group.Convolution
import Definitions.Def_Kyprianou_Ch03_IsSubordinator
import Definitions.Def_Kyprianou_Ch03_EntryAndHittingTimes
import Definitions.Def_Kyprianou_Ch05_RenewalMeasure
import Definitions.Def_Kyprianou_Ch05_KilledSubordinatorPotential
import Theorems.Thm_Kyprianou_Ch05_killedPotential_aliveLaplace_lintegral
import Theorems.Thm_Kyprianou_Ch05_killedPotential_expNeg_setLintegral
import Theorems.Thm_Kyprianou_Ch05_killedLaplaceExponent_nonneg
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
      (∫⁻ t in Set.Ici (0 : Real),
        ENNReal.ofReal (Real.exp (-q * t)) *
        ∫⁻ omega in {omega : Omega |
          (Real.toNNReal t : WithTop NNReal) < death omega},
          ENNReal.ofReal (Real.exp (-theta * Y (Real.toNNReal t) omega)) ∂P ∂volume) =
      (ENNReal.ofReal (q + Phi theta))⁻¹ := by
  intro q hq theta htheta
  have hPhi : 0 ≤ Phi theta :=
    Kyprianou.Ch05.killedLaplaceExponent_nonneg eta d Pi Phi hTriplet theta htheta
  have hstep : ∀ t ∈ Set.Ici (0 : Real),
      ENNReal.ofReal (Real.exp (-q * t)) *
        ∫⁻ omega in {omega : Omega |
          (Real.toNNReal t : WithTop NNReal) < death omega},
          ENNReal.ofReal (Real.exp (-theta * Y (Real.toNNReal t) omega)) ∂P =
      ENNReal.ofReal (Real.exp (-(q + Phi theta) * t)) := by
    intro t ht
    rw [Kyprianou.Ch05.killedPotential_aliveLaplace_lintegral P Y death eta d Pi Phi
      hKilled hTriplet hLaplaceLaw U hPotential t ht theta htheta]
    rw [← ENNReal.ofReal_mul (Real.exp_nonneg _), ← Real.exp_add]
    congr 1
    ring
  have hae : (fun t : Real => ENNReal.ofReal (Real.exp (-q * t)) *
        ∫⁻ omega in {omega : Omega |
          (Real.toNNReal t : WithTop NNReal) < death omega},
          ENNReal.ofReal (Real.exp (-theta * Y (Real.toNNReal t) omega)) ∂P)
      =ᵐ[volume.restrict (Set.Ici (0 : Real))]
      (fun t : Real => ENNReal.ofReal (Real.exp (-(q + Phi theta) * t))) := by
    filter_upwards [ae_restrict_mem measurableSet_Ici] with t ht
    exact hstep t ht
  rw [lintegral_congr_ae hae]
  exact Kyprianou.Ch05.killedPotential_expNeg_setLintegral (q + Phi theta)
    (add_nonneg hq hPhi)
