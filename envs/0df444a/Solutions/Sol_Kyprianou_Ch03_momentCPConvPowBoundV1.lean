-- Prove2me | solution 1 for Kyprianou.Ch03.momentCPConvPowBoundV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T12:54:42.230804+00:00
-- url     : https://prove2.me/submissions/ecab4c37-d6f0-47e0-a915-f9f6e581d16b

import Mathlib
import Definitions.Def_KSATSingleFlip_Connect_SoftField
import Definitions.Def_Kyprianou_Ch03_IsSubmultiplicative
import Theorems.Thm_Kyprianou_Ch03_momentCPConvStepBoundV1
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal
set_option autoImplicit false
theorem solution
    (mu : Measure Real) [IsFiniteMeasure mu]
    (g : Real → Real) (hg : Kyprianou.Ch03.IsSubmultiplicative g)
    (hg_meas : Measurable g)
    (c : Real) (hc : 0 < c)
    (hsub : ∀ x y : Real, g (x + y) ≤ c * g x * g y) (n : ℕ) :
    (∫⁻ x, ENNReal.ofReal (g x) ∂(KSATSingleFlip.Connect.convPow mu n)) ≤
      ENNReal.ofReal (g 0) *
        (ENNReal.ofReal c * (∫⁻ x, ENNReal.ofReal (g x) ∂mu)) ^ n := by
  let f (x : ℝ) := ENNReal.ofReal (g x)
  have hf : Measurable f := ENNReal.measurable_ofReal.comp hg_meas
  let r : ENNReal := ENNReal.ofReal c * (∫⁻ x, f x ∂mu)
  have hp (k : ℕ) : IsFiniteMeasure (KSATSingleFlip.Connect.convPow mu k) := by
    induction k with
    | zero => simp [KSATSingleFlip.Connect.convPow]; infer_instance
    | succ k ih =>
      letI := ih
      change IsFiniteMeasure (mu ∗ KSATSingleFlip.Connect.convPow mu k)
      infer_instance
  change (∫⁻ x, f x ∂(KSATSingleFlip.Connect.convPow mu n)) ≤ f 0 * r ^ n
  induction n with
  | zero => simp [KSATSingleFlip.Connect.convPow, lintegral_dirac, hf]
  | succ n ih =>
    letI := hp n
    change (∫⁻ x, f x ∂(mu ∗ KSATSingleFlip.Connect.convPow mu n)) ≤ _
    calc
      _ ≤ r * (∫⁻ x, f x ∂(KSATSingleFlip.Connect.convPow mu n)) :=
        Kyprianou.Ch03.momentCPConvStepBoundV1 mu g hg hg_meas _ c hc hsub
      _ ≤ r * (f 0 * r ^ n) := by gcongr
      _ = f 0 * r ^ (n + 1) := by rw [pow_succ]; ac_rfl
