-- Prove2me | solution 1 for Kyprianou.Ch01.harmonicReciprocalLIntegralFormula
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T13:21:46.853369+00:00
-- url     : https://prove2.me/submissions/ce3fe4f6-1233-4fdf-9e0b-fe0ff4bb9340

import Mathlib
import Definitions.Def_Kyprianou_Ch01_LampertiInverse
import Theorems.Thm_Kyprianou_Ch01_realHarmonicIntegralFormulaV2
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Kyprianou.Ch01 Set Filter Real
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Real-to-extended-real comparison for the finite harmonic integral. -/
theorem solution
    (C : ℝ) (hC : 0 < C) (s : ℝ≥0) :
    (∫⁻ r in Set.Ioc (0 : ℝ) (s : ℝ),
      (ENNReal.ofReal (C * (1 + r)))⁻¹ ∂volume) =
        ENNReal.ofReal (Real.log (1 + (s : ℝ)) / C) := by
  let f : ℝ → ℝ := fun r => 1 / (C * (1 + r))
  have hC0 : C ≠ 0 := ne_of_gt hC
  have hcont : ContinuousOn f (Set.Icc (0 : ℝ) (s : ℝ)) := by
    apply ContinuousOn.div continuousOn_const
    · exact continuousOn_const.mul (continuousOn_const.add continuousOn_id)
    · intro r hr
      have hr0 : 0 ≤ r := hr.1
      exact ne_of_gt (mul_pos hC (by linarith))
  have hIntIcc : IntegrableOn f (Set.Icc (0 : ℝ) (s : ℝ)) volume :=
    hcont.integrableOn_Icc
  have hInt : Integrable f (volume.restrict (Set.Ioc (0 : ℝ) (s : ℝ))) :=
    (integrableOn_Icc_iff_integrableOn_Ioc).mp hIntIcc
  have hnonneg : 0 ≤ᵐ[volume.restrict (Set.Ioc (0 : ℝ) (s : ℝ))] f := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    have hr0 : 0 ≤ r := le_of_lt hr.1
    exact le_of_lt (one_div_pos.mpr (mul_pos hC (by linarith)))
  have hfun : ∀ r : ℝ, f r = (1 / (1 + r)) / C := by
    intro r
    simp [f, div_eq_mul_inv, mul_inv_rev, mul_comm]
  have hEval : (∫ r in Set.Ioc (0 : ℝ) (s : ℝ), f r ∂volume) =
      Real.log (1 + (s : ℝ)) / C := by
    simp_rw [hfun]
    rw [integral_div]
    rw [Kyprianou.Ch01.realHarmonicIntegralFormulaV2]
  calc
    (∫⁻ r in Set.Ioc (0 : ℝ) (s : ℝ),
      (ENNReal.ofReal (C * (1 + r)))⁻¹ ∂volume) =
        ∫⁻ r in Set.Ioc (0 : ℝ) (s : ℝ), ENNReal.ofReal (f r) ∂volume := by
          apply lintegral_congr_ae
          filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
          have hr0 : 0 ≤ r := le_of_lt hr.1
          have hp : 0 < C * (1 + r) := mul_pos hC (by linarith)
          simpa only [f, one_div] using (ENNReal.ofReal_inv_of_pos hp).symm
    _ = ENNReal.ofReal (∫ r in Set.Ioc (0 : ℝ) (s : ℝ), f r ∂volume) :=
      (ofReal_integral_eq_lintegral_ofReal hInt hnonneg).symm
    _ = ENNReal.ofReal (Real.log (1 + (s : ℝ)) / C) := by rw [hEval]
