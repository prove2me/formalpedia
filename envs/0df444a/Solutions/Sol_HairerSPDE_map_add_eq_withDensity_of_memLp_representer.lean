-- Prove2me | solution 1 for HairerSPDE.map_add_eq_withDensity_of_memLp_representer
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-14T12:23:18.09172+00:00
-- url     : https://prove2.me/submissions/626ae62f-8e3b-4634-860b-446fb5ca5218

import Mathlib
import Definitions.Def_HairerSPDE_CameronMartin
import Theorems.Thm_HairerSPDE_charFunDual_map_add
import Theorems.Thm_HairerSPDE_charFunDual_withDensity_exp_of_representer

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology

-- The remote wrapper looks up an unqualified top-level `solution`, so the
-- target namespace is opened rather than entered.
open HairerSPDE

theorem solution {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B] [MeasurableSpace B]
    [BorelSpace B] [CompleteSpace B] [SecondCountableTopology B]
    (μ : Measure B) [IsGaussian μ] (hμ : μ[id] = 0) (h : B) (h' : B → ℝ)
    (h'meas : Measurable h') (h'mem : MemLp h' 2 μ)
    (h'rep : ∀ L : StrongDual ℝ B, ∫ x, h' x * L x ∂μ = L h)
    (h'orth : (∀ g : B → ℝ, MemLp g 2 μ →
        (∀ L : StrongDual ℝ B, ∫ x, g x * L x ∂μ = 0) → ∫ x, h' x * g x ∂μ = 0)) :
    μ.map (fun x : B => x + h) =
      μ.withDensity
        (fun x : B => ENNReal.ofReal (Real.exp (h' x - (∫ y, (h' y) ^ 2 ∂μ) / 2))) := by
  obtain ⟨hfin, hD2⟩ :=
    charFunDual_withDensity_exp_of_representer μ hμ h h' h'meas h'mem h'rep h'orth
  haveI := hfin
  apply Measure.ext_of_charFunDual
  funext L
  rw [charFunDual_map_add μ hμ h L, hD2 L]
