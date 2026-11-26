-- Prove2me | solution 1 for Kyprianou.Ch05.killedPotential_expIntegrableOn
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T16:13:46.939584+00:00
-- url     : https://prove2.me/submissions/fa170438-6e6e-41de-b721-b294c1f0de64

import Definitions.Def_Kyprianou_Ch05_ExponentialPassageMoments
import Mathlib
import Theorems.Thm_Kyprianou_Ch05_killedPotential_laplaceTransform
import Definitions.Def_Kyprianou_Ch05_RegularVariation
import Definitions.Def_Kyprianou_Ch05_KilledSubordinatorPotential
import Definitions.Def_Kyprianou_Ch05_FirstPassageObservables
import Definitions.Def_Kyprianou_Ch05_WeakPassageObservables
open MeasureTheory Filter ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch05
open Classical
theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (Y Yleft : NNReal → Omega → Real)
    (death : Omega → WithTop NNReal)
    (d : Real) (Pi : Measure Real) (Phi : Real → Real)
    (U : Real → Measure Real)
    (hKilled : IsKilledSubordinator P Y death 0)
    (hTriplet : IsKilledLaplaceTriplet 0 d Pi Phi)
    (hLaplaceLaw : ∀ (t : NNReal) (theta : Real), 0 ≤ theta →
      (∫ omega, Real.exp (-theta * Y t omega) ∂P) =
        Real.exp (-(t : Real) * Phi theta))
    (hPotential : IsKilledPotentialFamily P Y death U)
    (hLeft : IsLeftLimitVersion P Y Yleft)
    (alpha beta : Real) (ha : 0 ≤ alpha) (hb : 0 ≤ beta)
    (hpos : 0 < alpha + Phi beta) (B : Set Real) :
    IntegrableOn (fun z : Real => Real.exp (-beta*z)) B (U alpha) := by
  refine ⟨(by fun_prop), ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall
    fun z => (Real.exp_pos (-beta*z)).le)]
  have h := killedPotential_laplaceTransform P Y death 0 d Pi Phi
    hKilled hTriplet (by simpa using hLaplaceLaw) U hPotential alpha ha beta hb
  apply lt_of_le_of_lt (lintegral_mono' Measure.restrict_le_self le_rfl)
  rw [h]
  exact ENNReal.inv_lt_top.mpr (ENNReal.ofReal_pos.mpr hpos)
