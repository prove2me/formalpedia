-- Prove2me | solution 1 for Kyprianou.Ch05.exercise56_stableLevyDensity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T13:01:49.316901+00:00
-- url     : https://prove2.me/submissions/8d2528a6-f7c2-4356-bb07-4098002b02ad

import Mathlib
import Definitions.Def_Kyprianou_Ch05_KilledSubordinatorPotential
import Definitions.Def_Kyprianou_Ch05_FirstPassageObservables
import Theorems.Thm_Kyprianou_Ch01_stableGammaIntegral
import Theorems.Thm_Kyprianou_Ch01_stableGammaNegativeRecurrence
import Theorems.Thm_Kyprianou_Ch05_positiveLevyDeficitIntegrable
import Theorems.Thm_Kyprianou_Ch05_stableLevyDeficitOfGamma
import Theorems.Thm_Kyprianou_Ch05_positiveLevyMeasureEqOfDeficitPlusDrift
open MeasureTheory Filter ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch05

/-- Identify the stable Levy measure from its deficit transform. -/
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
  (Pi =
      ((volume : Measure Real).restrict (Set.Ioi 0)).withDensity
        (fun z : Real =>
          ENNReal.ofReal (z ^ (-1-alpha) / (-Real.Gamma (-alpha)))))
  := by
  rcases hTriplet with ⟨_, _, hPi, hm, hPhi⟩
  have hg : 0 < -Real.Gamma (-alpha) := by
    rw [Kyprianou.Ch01.stableGammaNegativeRecurrence alpha hAlpha.1 hAlpha.2]
    have h := Real.Gamma_pos_of_pos (sub_pos.mpr hAlpha.2)
    exact neg_pos.mpr (div_neg_of_neg_of_pos (neg_neg_of_pos h) hAlpha.1)
  apply positiveLevyMeasureEqOfDeficitPlusDrift Pi _ d hPi
  · rw [withDensity_apply _ measurableSet_Iic, Measure.restrict_restrict measurableSet_Iic]
    have he : Set.Iic (0 : Real) ∩ Set.Ioi 0 = ∅ := by
      ext x
      simp only [Set.mem_inter_iff, Set.mem_Iic, Set.mem_Ioi, Set.mem_empty_iff_false]
      exact iff_false_intro (fun h => (not_lt_of_ge h.1) h.2)
    simp [he]
  · exact fun t ht => positiveLevyDeficitIntegrable Pi hm t ht
  · intro t ht
    exact (stableLevyDeficitOfGamma alpha t hAlpha.1 hAlpha.2 ht hg
      (Kyprianou.Ch01.stableGammaIntegral alpha t hAlpha.1 hAlpha.2 ht)).1
  · intro t ht
    have h := hPhi t ht.le
    rw [hStablePhi t ht.le, zero_add] at h
    exact h.symm.trans (stableLevyDeficitOfGamma alpha t hAlpha.1 hAlpha.2 ht hg
      (Kyprianou.Ch01.stableGammaIntegral alpha t hAlpha.1 hAlpha.2 ht)).2.symm
