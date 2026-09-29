-- Prove2me | solution 1 for HairerSPDE.charFunDual_withDensity_exp_of_representer
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-15T06:10:27.760571+00:00
-- url     : https://prove2.me/submissions/b68571c6-b398-4709-b49a-6fe0436ad872

import Mathlib
import Definitions.Def_HairerSPDE_CameronMartin
import Theorems.Thm_HairerSPDE_joint_gaussian_of_memLp_closure
import Theorems.Thm_HairerSPDE_charFun_tilt_of_joint_gaussian

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology

open HairerSPDE

theorem solution {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B] [MeasurableSpace B]
    [BorelSpace B] [CompleteSpace B] [SecondCountableTopology B]
    (μ : Measure B) [IsGaussian μ] (hμ : μ[id] = 0) (h : B) (h' : B → ℝ)
    (h'meas : Measurable h') (h'mem : MemLp h' 2 μ)
    (h'rep : ∀ L : StrongDual ℝ B, ∫ x, h' x * L x ∂μ = L h)
    (h'orth : (∀ g : B → ℝ, MemLp g 2 μ →
        (∀ L : StrongDual ℝ B, ∫ x, g x * L x ∂μ = 0) → ∫ x, h' x * g x ∂μ = 0)) :
    IsFiniteMeasure (μ.withDensity (fun x : B => ENNReal.ofReal (Real.exp (h' x - (∫ y, (h' y) ^ 2 ∂μ) / 2))))
    ∧ ∀ L : StrongDual ℝ B, charFunDual (μ.withDensity (fun x : B => ENNReal.ofReal (Real.exp (h' x - (∫ y, (h' y) ^ 2 ∂μ) / 2)))) L = Complex.exp ((L h) * Complex.I - covarianceBilinDual μ L L / 2) := by
  have hjoint := joint_gaussian_of_memLp_closure μ hμ h' h'meas h'mem h'orth
  exact charFun_tilt_of_joint_gaussian μ hμ h h' h'meas h'mem h'rep hjoint
