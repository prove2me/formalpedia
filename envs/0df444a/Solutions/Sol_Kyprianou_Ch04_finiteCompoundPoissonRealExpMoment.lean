-- Prove2me | solution 1 for Kyprianou.Ch04.finiteCompoundPoissonRealExpMoment
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T08:07:14.656308+00:00
-- url     : https://prove2.me/submissions/0c569846-f448-470a-a31d-683db48b10fc

import Mathlib
import Definitions.Def_KSATSingleFlip_Connect_SoftField
import Theorems.Thm_KSATSingleFlip_Connect_compound_poisson_exponential_moment
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Convert the finite compound Poisson extended moment to a real moment. -/
theorem solution
    (nu : Measure Real) [IsFiniteMeasure nu] (beta : Real)
    (h : Integrable (fun x : Real => Real.exp (beta*x)) nu) :
    Integrable (fun x : Real => Real.exp (beta*x))
        (KSATSingleFlip.Connect.compoundPoisson nu) ∧
      (∫ x, Real.exp (beta*x) ∂(KSATSingleFlip.Connect.compoundPoisson nu)) =
        Real.exp (∫ x, (Real.exp (beta*x)-1) ∂nu) := by
  let f (x : ℝ) := Real.exp (beta*x)
  let J := KSATSingleFlip.Connect.compoundPoisson nu
  have hn (x : ℝ) : 0 ≤ f x := (Real.exp_pos _).le
  have hfin := (hasFiniteIntegral_iff_ofReal (Eventually.of_forall hn)).mp h.2
  have hcp := KSATSingleFlip.Connect.compound_poisson_exponential_moment nu beta hfin.ne
  change (∫⁻ x, ENNReal.ofReal (f x) ∂J) = _ at hcp
  have hi : Integrable f J := ⟨by dsimp [f]; fun_prop,
    (hasFiniteIntegral_iff_ofReal (Eventually.of_forall hn)).mpr
      (hcp.trans_lt ENNReal.ofReal_lt_top)⟩
  refine ⟨hi, ?_⟩
  rw [← ofReal_integral_eq_lintegral_ofReal h (Eventually.of_forall hn),
    ENNReal.toReal_ofReal (integral_nonneg hn),
    ← ofReal_integral_eq_lintegral_ofReal hi (Eventually.of_forall hn)] at hcp
  have he := congrArg ENNReal.toReal hcp
  rw [ENNReal.toReal_ofReal (integral_nonneg hn),
    ENNReal.toReal_ofReal (by positivity)] at he
  change (∫ x, f x ∂J) = _
  rw [he, ← Real.exp_add, integral_sub h (integrable_const 1), integral_const]
  simp [Measure.real, smul_eq_mul, sub_eq_add_neg, add_comm, f]
