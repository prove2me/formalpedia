-- Prove2me | solution 1 for Kyprianou.Ch05.exercise56_stablePotentialDensity
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T12:45:20.00559+00:00
-- url     : https://prove2.me/submissions/1daca94e-d4fc-4677-b5ba-19eba2872af6
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_Kyprianou_Ch05_KilledSubordinatorPotential
import Definitions.Def_Kyprianou_Ch05_FirstPassageObservables
import Theorems.Thm_Kyprianou_Ch01_stableGammaKernelIntegral
import Theorems.Thm_Kyprianou_Ch05_killedPotential_laplaceTransform
import Theorems.Thm_Kyprianou_Ch05_stableGammaDensityLaplaceOfKernelIntegral
import Theorems.Thm_Kyprianou_Ch05_measureEqOfFinitePositiveLaplace
open MeasureTheory Filter ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch05

/-- Stable potential density by the Gamma transform and measure uniqueness. -/
theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (Y Yleft : NNReal → Omega → Real)
    (death : Omega → WithTop NNReal)
    (d : Real) (Pi : Measure Real) (Phi : Real → Real)
    (U : Real → Measure Real)
    (alpha : Real) (hAlpha : 0 < alpha ∧ alpha < 1)
    (hKilled : IsKilledSubordinator P Y death 0)
    (hTriplet : IsKilledLaplaceTriplet 0 d Pi Phi)
    (hLaplaceLaw : ∀ (t : NNReal) (theta : Real), 0 ≤ theta →
      (∫ omega, Real.exp (-theta * Y t omega) ∂P) =
        Real.exp (-(t : Real) * Phi theta))
    (hStablePhi : ∀ theta : Real, 0 ≤ theta → Phi theta = theta ^ alpha)
    (hPotential : IsKilledPotentialFamily P Y death U)
    (hLeft : IsLeftLimitVersion P Y Yleft) :
  ((U 0) =
      ((volume : Measure Real).restrict (Set.Ioi 0)).withDensity
        (fun z : Real =>
          ENNReal.ofReal (z ^ (alpha-1) / Real.Gamma alpha))) := by
  have hL (theta : Real) (ht : 0 < theta) :
      (∫⁻ x : Real, ENNReal.ofReal (Real.exp (-theta * x)) ∂(U 0)) =
        (ENNReal.ofReal (theta ^ alpha))⁻¹ := by
    have h := killedPotential_laplaceTransform P Y death 0 d Pi Phi
      hKilled hTriplet (by simpa using hLaplaceLaw) U hPotential
      0 le_rfl theta ht.le
    simpa [hStablePhi theta ht.le] using h
  apply measureEqOfFinitePositiveLaplace
  · intro theta ht
    rw [hL theta ht]
    exact ENNReal.inv_lt_top.mpr (ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos ht alpha))
  · intro theta ht
    have hk := Kyprianou.Ch01.stableGammaKernelIntegral (1-alpha) theta
      (sub_pos.mpr hAlpha.2) (by linarith [hAlpha.1]) ht
    rw [show -(1-alpha) = alpha-1 by ring,
      show 1-(1-alpha) = alpha by ring] at hk
    exact (hL theta ht).trans
      (stableGammaDensityLaplaceOfKernelIntegral alpha theta
        hAlpha.1 hAlpha.2 ht hk).symm
