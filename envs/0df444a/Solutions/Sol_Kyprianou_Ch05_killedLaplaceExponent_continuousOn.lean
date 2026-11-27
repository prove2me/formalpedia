-- Prove2me | solution 1 for Kyprianou.Ch05.killedLaplaceExponent_continuousOn
-- status  : ACCEPTED   (prove)
-- author  : @daga2
-- created : 2026-11-27T05:13:01.310349+00:00
-- url     : https://prove2.me/submissions/ba9631bf-6325-4fc3-9a61-dd3296424709

import Mathlib
import Definitions.Def_Kyprianou_Ch05_RegularVariation
import Definitions.Def_Kyprianou_Ch05_KilledSubordinatorPotential
import Definitions.Def_Kyprianou_Ch05_MonotoneDensity
open MeasureTheory Filter ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false

open Kyprianou.Ch05 Set

/-- H-Phi: the Laplace exponent is continuous on [0, ∞), by dominated
convergence on the triplet integral, dominated by min(1, x). -/
theorem solution
    (eta d : Real) (Pi : Measure Real) (Phi : Real → Real)
    (hTriplet : IsKilledLaplaceTriplet eta d Pi Phi) :
    ContinuousOn Phi (Set.Ici (0 : Real)) := by
  obtain ⟨heta, hd, hPi0, hInt, hPhiEq⟩ := hTriplet
  have hMinInt : Integrable (fun x : Real => min 1 x) (Pi.restrict (Set.Ioi (0 : Real))) := by
    refine ⟨?_, ?_⟩
    · exact ((continuous_const.min continuous_id : Continuous fun x : Real => min 1 x)).aestronglyMeasurable
    · show (∫⁻ a, ‖(min 1 a : Real)‖ₑ ∂(Pi.restrict (Set.Ioi (0 : Real)))) < ⊤
      have h1 : (∫⁻ a, ‖(min 1 a : Real)‖ₑ ∂(Pi.restrict (Set.Ioi (0 : Real))))
          = ∫⁻ a in Set.Ioi (0 : Real), ENNReal.ofReal (min 1 a) ∂Pi := by
        apply MeasureTheory.lintegral_congr_ae
        filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with a ha
        rw [Real.enorm_eq_ofReal (le_min zero_le_one (le_of_lt ha))]
      rw [h1]
      exact hInt
  have hIntCont : ContinuousOn
      (fun theta : Real => ∫ x in Set.Ioi (0 : Real), (1 - Real.exp (-theta * x)) ∂Pi)
      (Set.Ici (0 : Real)) := by
    intro theta0 htheta0
    have htheta0nn : (0 : Real) ≤ theta0 := Set.mem_Ici.mp htheta0
    show Tendsto (fun theta : Real => ∫ x in Set.Ioi (0 : Real),
        (1 - Real.exp (-theta * x)) ∂Pi) (nhdsWithin theta0 (Set.Ici (0 : Real)))
        (nhds (∫ x in Set.Ioi (0 : Real), (1 - Real.exp (-theta0 * x)) ∂Pi))
    have hBoundInt : Integrable (fun x : Real => (theta0 + 1) * min 1 x)
        (Pi.restrict (Set.Ioi (0 : Real))) := hMinInt.const_mul (theta0 + 1)
    apply MeasureTheory.tendsto_integral_filter_of_dominated_convergence
      (fun x : Real => (theta0 + 1) * min 1 x) _ _ hBoundInt _
    · -- measurability of each integrand
      apply Filter.Eventually.of_forall
      intro theta
      exact (by fun_prop : Continuous fun x : Real => 1 - Real.exp (-theta * x)).aestronglyMeasurable
    · -- domination on a neighbourhood of theta0
      filter_upwards [mem_nhdsWithin_of_mem_nhds
          (Iic_mem_nhds (by linarith : theta0 < theta0 + 1)), self_mem_nhdsWithin]
        with theta hIic hIci
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with x hx
      have htheta0 : (0 : Real) ≤ theta := hIci
      have htheta1 : theta ≤ theta0 + 1 := hIic
      have hnn : (0 : Real) ≤ 1 - Real.exp (-theta * x) := by
        apply sub_nonneg.mpr
        rw [Real.exp_le_one_iff]
        exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr htheta0) hx.le
      rw [Real.norm_eq_abs, abs_of_nonneg hnn]
      have hle1 : 1 - Real.exp (-theta * x) ≤ min 1 (theta * x) := by
        apply le_min
        · exact sub_le_self 1 (Real.exp_pos _).le
        · have h := Real.add_one_le_exp (-(theta * x))
          rw [← neg_mul] at h
          linarith
      have hle2 : min 1 (theta * x) ≤ min 1 ((theta0 + 1) * x) :=
        min_le_min le_rfl (mul_le_mul_of_nonneg_right htheta1 hx.le)
      have hle3 : min 1 ((theta0 + 1) * x) ≤ (theta0 + 1) * min 1 x := by
        rw [mul_min_of_nonneg _ _ (by linarith : (0 : Real) ≤ theta0 + 1), mul_one]
        exact min_le_min (by linarith) le_rfl
      exact le_trans (le_trans hle1 hle2) hle3
    · -- pointwise convergence in theta
      apply Filter.Eventually.of_forall
      intro x
      exact ((by fun_prop : Continuous fun theta : Real => 1 - Real.exp (-theta * x)).tendsto
        theta0).mono_left nhdsWithin_le_nhds
  refine ContinuousOn.congr ?_ (fun theta htheta => hPhiEq theta htheta)
  exact (continuousOn_const.add (continuousOn_const.mul continuousOn_id)).add hIntCont
