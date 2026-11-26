-- Prove2me | solution 2 for Kyprianou.Ch05.regularVariationPotentialLimitAtInfinity
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T21:46:44.927392+00:00
-- url     : https://prove2.me/submissions/71ee0e6b-05f4-4a98-9f42-bc4cc26f054f
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_Kyprianou_Ch05_RegularVariation
import Definitions.Def_Kyprianou_Ch05_RenewalMeasure
import Definitions.Def_Kyprianou_Ch05_KilledSubordinatorPotential
import Definitions.Def_Kyprianou_Ch05_FirstPassageObservables
import Definitions.Def_Kyprianou_Ch05_WeakPassageObservables
import Theorems.Thm_Kyprianou_Ch05_potentialSupportNonnegative
import Theorems.Thm_Kyprianou_Ch05_potentialAllScalesFromLaplaceRatios
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
  have hsup := potentialSupportNonnegative P Y death U hKilled hPotential
  have hLap (t : Real) (ht : 0 < t) :
      positiveLaplace (U 0) t = (ENNReal.ofReal (Phi t))⁻¹ := by
    simpa [positiveLaplace] using
      killedPotential_laplaceTransform P Y death 0 d Pi Phi hKilled hTriplet
        (by simpa using hLaplaceLaw) U hPotential 0 le_rfl t ht.le
  intro a ha
  have he : ∀ᶠ x : Real in nhdsWithin (0 : Real) (Set.Ioi 0), 0 < x :=
    self_mem_nhdsWithin
  have hscale : Tendsto (fun x : Real => a*x) (nhdsWithin (0 : Real) (Set.Ioi 0))
      (nhdsWithin (0 : Real) (Set.Ioi 0)) := by
    apply tendsto_nhdsWithin_iff.mpr
    have hi : Tendsto (fun x : Real => x) (nhdsWithin (0 : Real) (Set.Ioi 0)) (nhds 0) :=
      tendsto_id.mono_left nhdsWithin_le_nhds
    refine ⟨by simpa only [mul_zero] using hi.const_mul a,?_⟩
    filter_upwards [he] with x hx
    exact mul_pos ha hx
  exact potentialAllScalesFromLaplaceRatios (U 0) Phi alpha
    (nhdsWithin (0 : Real) (Set.Ioi 0)) atTop hAlpha.1 hsup hRV.1 hLap
    he tendsto_inv_nhdsGT_zero hRV.2 a ha hscale
