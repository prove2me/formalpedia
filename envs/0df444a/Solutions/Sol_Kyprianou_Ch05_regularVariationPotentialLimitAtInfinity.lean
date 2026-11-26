-- Prove2me | solution 1 for Kyprianou.Ch05.regularVariationPotentialLimitAtInfinity
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T20:40:35.130944+00:00
-- url     : https://prove2.me/submissions/e57108bb-34e3-40f3-ad16-ee70d4c43ec8
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
import Theorems.Thm_Kyprianou_Ch05_karamataTauberianZeroCumulativeFinite
import Theorems.Thm_Kyprianou_Ch05_killedPotential_laplaceTransform
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
    (hRV : RegularlyVaryingAtInfinity Phi alpha) :
  (∀ lambda : Real, 0 < lambda →
        Tendsto
          (fun x : Real =>
            ((U 0) (Set.Icc (0 : Real) (lambda * x))).toReal *
              Phi (1 / x))
          (nhdsWithin (0 : Real) (Set.Ioi 0))
          (nhds (lambda ^ alpha / Real.Gamma (1+alpha)))) := by
  obtain ⟨L,hL,hPhi,hLap⟩ :=
    (potentialLaplaceAsymptoticsV2 P Y death d Pi Phi hKilled hTriplet hLaplaceLaw
      U hPotential alpha hAlpha).2 hRV
  have hsup := potentialSupportNonnegative P Y death U hKilled hPotential
  have hfin (t : Real) (ht : 0 < t) : positiveLaplace (U 0) t ≠ ⊤ := by
    have h := killedPotential_laplaceTransform P Y death 0 d Pi Phi hKilled hTriplet
      (by simpa using hLaplaceLaw) U hPotential 0 le_rfl t ht.le
    rw [positiveLaplace,h]
    simp [ENNReal.inv_ne_top, ENNReal.ofReal_ne_zero_iff.mpr (hRV.1 t ht)]
  have hCum := (karamataTauberianZeroCumulativeFinite (U 0) L alpha hL hAlpha.1 hsup hfin).mp hLap
  exact (potentialScalingLimitsV2 (U 0) Phi L alpha hAlpha.1 hPhi).2 hL hCum
