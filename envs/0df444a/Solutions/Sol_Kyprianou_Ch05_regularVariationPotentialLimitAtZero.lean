-- Prove2me | solution 1 for Kyprianou.Ch05.regularVariationPotentialLimitAtZero
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T20:40:35.035823+00:00
-- url     : https://prove2.me/submissions/ec6d60c2-6a27-4263-8de0-42a5eeb084ea
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_Kyprianou_Ch05_RegularVariation
import Definitions.Def_Kyprianou_Ch05_RenewalMeasure
import Definitions.Def_Kyprianou_Ch05_KilledSubordinatorPotential
import Definitions.Def_Kyprianou_Ch05_FirstPassageObservables
import Definitions.Def_Kyprianou_Ch05_WeakPassageObservables
import Theorems.Thm_Kyprianou_Ch05_potentialSupportNonnegative
import Theorems.Thm_Kyprianou_Ch05_potentialLaplaceAsymptoticsV2
import Theorems.Thm_Kyprianou_Ch05_potentialScalingLimitsV2
import Theorems.Thm_Kyprianou_Ch05_karamataTauberianInfinity
open MeasureTheory Filter ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false

open Kyprianou.Ch05 Set

/-- Corrected potential limit via the reciprocal slow factor and Karamata. -/
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
    (alpha : Real) (hAlpha : 0 ≤ alpha ∧ alpha ≤ 1)
    (hRV : RegularlyVaryingAtZero Phi alpha) :
  (∀ lambda : Real, 0 < lambda →
        Tendsto
          (fun x : Real =>
            ((U 0) (Set.Icc (0 : Real) (lambda * x))).toReal *
              Phi (1 / x))
          atTop
          (nhds (lambda ^ alpha / Real.Gamma (1+alpha)))) := by
  obtain ⟨L,hL,hPhi,hLap⟩ :=
    (potentialLaplaceAsymptoticsV2 P Y death d Pi Phi hKilled hTriplet hLaplaceLaw
      U hPotential alpha hAlpha).1 hRV
  have hsup := potentialSupportNonnegative P Y death U hKilled hPotential
  have hCum := (karamataTauberianInfinity (U 0) L alpha hL hAlpha.1 hsup).mp hLap
  exact (potentialScalingLimitsV2 (U 0) Phi L alpha hAlpha.1 hPhi).1 hL hCum
