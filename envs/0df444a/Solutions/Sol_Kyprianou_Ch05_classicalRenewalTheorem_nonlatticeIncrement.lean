-- Prove2me | solution 1 for Kyprianou.Ch05.classicalRenewalTheorem_nonlatticeIncrement
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T16:58:08.057873+00:00
-- url     : https://prove2.me/submissions/77a020d6-fd2b-4213-9a5a-79e49dad9e9b

import Mathlib
import Definitions.Def_Kyprianou_Ch05_RenewalMeasure
import Theorems.Thm_AvramDividend_Classical_avram_p4_f6_renewal_cdf_monotone
import Theorems.Thm_SmithRegenerative_Equilibrium_theorem_A_a
import Theorems.Thm_Kyprianou_Ch05_smithCycleAperiodicCompatibility
import Theorems.Thm_Kyprianou_Ch05_smithZeroDelayRenewalIdentity
import Theorems.Thm_Kyprianou_Ch05_smithFiniteMeanCompatibility
import Theorems.Thm_Kyprianou_Ch05_smithBlackwellIndicatorAdmissible
import Theorems.Thm_Kyprianou_Ch05_smithBlackwellIndicatorVolume
import Theorems.Thm_Kyprianou_Ch05_smithBlackwellIndicatorIntervalIntegral
open MeasureTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch05

/-- Transfer Smith's key renewal theorem to the Chapter 5 interval limit. -/
theorem solution
    (F : Measure Real) [IsProbabilityMeasure F]
    (hSupport : F (Set.Iio (0 : Real)) = 0)
    (hFiniteMean : Integrable (fun x : Real => x) F)
    (hPositiveMean : 0 < ∫ x : Real, x ∂F) :
    let mu := ∫ x : Real, x ∂F
    let V := renewalMeasure F
    (NonLatticeMeasure F →
      ∀ y : Real, 0 < y →
        Tendsto (fun x : Real => (V (Set.Ioc x (x+y))).toReal)
          atTop (nhds (y / mu))) := by
  dsimp only
  intro hnl y hy
  let psi : Real → Real := (Set.Ico 0 y).indicator (fun _ => 1)
  obtain ⟨hc, ha⟩ := smithCycleAperiodicCompatibility F hSupport hPositiveMean hnl
  obtain ⟨hp, hb, ham, hi⟩ := smithBlackwellIndicatorAdmissible y hy
  have hd : SmithRegenerative.Equilibrium.IsDelayLaw (Measure.dirac 0) := by
    constructor <;> simp [Measure.dirac_apply, measurableSet_Iio]
  have hm := smithFiniteMeanCompatibility F hSupport hFiniteMean
  have hV := smithZeroDelayRenewalIdentity F
  have hvol : (∫ v in Set.Ioi 0, psi v) = y := smithBlackwellIndicatorVolume y hy
  have H := (SmithRegenerative.Equilibrium.theorem_A_a F (Measure.dirac 0)
    hc hd ha psi hp hb ham hi).2 (by rw [hm]; exact ENNReal.ofReal_ne_top)
  rw [hV, hm, hvol] at H
  have H' : Tendsto (fun t : Real => ∫ s in Set.Icc 0 t, psi (t-s) ∂renewalMeasure F)
      atTop (nhds (y / (∫ x : Real, x ∂F))) := by
    simpa [ENNReal.toReal_ofReal hPositiveMean.le, div_eq_mul_inv, mul_comm] using H
  have hshift : Tendsto (fun x : Real => x + y) atTop atTop :=
    tendsto_atTop_add_const_right atTop y tendsto_id
  apply (H'.comp hshift).congr'
  filter_upwards [eventually_ge_atTop (0 : Real)] with x hx
  exact smithBlackwellIndicatorIntervalIntegral (renewalMeasure F) x y hx
