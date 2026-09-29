-- Prove2me | solution 1 for HairerSPDE.charFunDual_map_add
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-14T12:29:21.342957+00:00
-- url     : https://prove2.me/submissions/da934154-c89e-48fd-b624-d31ce360dc7c

import Mathlib
import Definitions.Def_HairerSPDE_CameronMartin

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology

-- The remote wrapper looks up an unqualified top-level `solution`, so the
-- target namespace is opened rather than entered.
open HairerSPDE

theorem solution {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B] [MeasurableSpace B]
    [BorelSpace B] [CompleteSpace B] [SecondCountableTopology B]
    (μ : Measure B) [IsGaussian μ] (hμ : μ[id] = 0) (h : B)
    (L : StrongDual ℝ B) :
    charFunDual (μ.map (fun x : B => x + h)) L
      = Complex.exp ((L h) * Complex.I - covarianceBilinDual μ L L / 2) := by
  have hmeas : AEMeasurable (fun x : B => x + h) μ := (measurable_add_const h).aemeasurable
  -- `Continuous.mul` does not unify against a lambda goal (Pi.mul_apply does not
  -- unfold during elaboration); discharge the continuity structurally instead.
  have hcont : Continuous (fun v : B => Complex.exp ((L v) * Complex.I)) := by
    fun_prop
  rw [charFunDual_apply, integral_map hmeas hcont.aestronglyMeasurable]
  simp_rw [map_add, Complex.ofReal_add, add_mul, Complex.exp_add]
  rw [integral_mul_const, ← charFunDual_apply, IsGaussian.charFunDual_eq', hμ, map_zero,
    Complex.ofReal_zero, zero_mul, zero_sub, ← Complex.exp_add]
  congr 1
  ring
