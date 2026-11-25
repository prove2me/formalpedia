-- Prove2me | solution 1 for Kyprianou.Ch04.exercise46LowerHeightLaplaceLimitV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T21:48:26.859805+00:00
-- url     : https://prove2.me/submissions/b3cfb249-3b3f-4161-a37e-65ea5accdd29

import Mathlib
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (A : Nat → Omega → Real) (J : Omega → Real)
    (phi : Real) (hphi : 0 ≤ phi)
    (hA : ∀ n, AEMeasurable (A n) P)
    (hpos : ∀ n, ∀ᵐ w ∂P, 0 < A n w)
    (hlim : ∀ᵐ w ∂P, Tendsto (fun n => A n w) atTop (nhds (J w))) :
    Tendsto (fun n => ∫ w, Real.exp (-phi * A n w) ∂P) atTop
      (nhds (∫ w, Real.exp (-phi * J w) ∂P)) := by
  apply tendsto_integral_of_dominated_convergence (fun _ => (1 : Real))
  · intro n
    exact (Real.measurable_exp.comp_aemeasurable (aemeasurable_const.mul (hA n))).aestronglyMeasurable
  · exact integrable_const 1
  · intro n
    filter_upwards [hpos n] with w hw
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.exp_pos _).le]
    exact Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hphi) hw.le)
  · filter_upwards [hlim] with w hw
    exact Real.continuous_exp.continuousAt.tendsto.comp (tendsto_const_nhds.mul hw)
