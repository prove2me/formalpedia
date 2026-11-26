-- Prove2me | solution 1 for Kyprianou.Ch05.karamataGammaCumulativePositive
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T21:47:19.307875+00:00
-- url     : https://prove2.me/submissions/6a1924ed-4b8a-456f-b09d-58bb7d69a66f

import Mathlib
import Definitions.Def_Kyprianou_Ch05_RegularVariation
import Definitions.Def_Kyprianou_Ch05_MonotoneDensity
open MeasureTheory Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch05

/-- Gamma-normalised power density has the required cumulative mass at one. -/
theorem solution
    (rho : Real) (hrho : 0 < rho) :
    (((volume.restrict (Ioi (0 : Real))).withDensity
      (fun z : Real => ENNReal.ofReal (z^(rho-1)/Real.Gamma rho))) (Icc 0 1)).toReal =
      1/Real.Gamma (1+rho) := by
  have hg := Real.Gamma_pos_of_pos hrho
  rw [withDensity_apply _ measurableSet_Icc]
  rw [Measure.restrict_restrict measurableSet_Icc]
  have hset : Icc (0 : Real) 1 ∩ Ioi 0 = Ioc 0 1 := by
    ext z
    constructor
    · intro hz
      exact ⟨hz.2,hz.1.2⟩
    · intro hz
      exact ⟨⟨hz.1.le,hz.2⟩,hz.1⟩
  rw [hset]
  have hnn : 0 ≤ᵐ[volume.restrict (Ioc (0 : Real) 1)]
      (fun z : Real => z^(rho-1)/Real.Gamma rho) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with z hz
    exact div_nonneg (Real.rpow_nonneg hz.1.le _) hg.le
  rw [← integral_eq_lintegral_of_nonneg_ae hnn (by fun_prop)]
  rw [integral_div,← intervalIntegral.integral_of_le (by norm_num : (0 : Real) ≤ 1),
    integral_rpow (Or.inl (by linarith : -1 < rho-1))]
  rw [show rho-1+1=rho by ring,Real.one_rpow,Real.zero_rpow hrho.ne',sub_zero,
    show 1+rho=rho+1 by ring,Real.Gamma_add_one hrho.ne']
  field_simp [hrho.ne',hg.ne']
