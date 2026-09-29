-- Prove2me | solution 1 for HairerSPDE.map_add_exists_pos_withDensity_of_finite_norm
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-14T12:10:36.49704+00:00
-- url     : https://prove2.me/submissions/2c6e12fc-1ed9-4f92-ab30-4a21b9a93b6f

import Mathlib
import Definitions.Def_HairerSPDE_CameronMartin
import Theorems.Thm_HairerSPDE_exists_memLp_two_representer_of_finite_norm
import Theorems.Thm_HairerSPDE_map_add_eq_withDensity_of_memLp_representer

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology

-- The remote wrapper looks up an unqualified top-level `solution`, so the
-- target namespace is opened rather than entered.
open HairerSPDE

theorem solution {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B] [MeasurableSpace B]
    [BorelSpace B] [CompleteSpace B] [SecondCountableTopology B]
    (μ : Measure B) [IsGaussian μ] (hμ : μ[id] = 0) (h : B)
    (hh : cameronMartinNorm μ h ≠ ∞) :
    ∃ f : B → ℝ≥0∞, Measurable f ∧ (∀ x : B, f x ≠ 0) ∧
      μ.map (fun x : B => x + h) = μ.withDensity f := by
  obtain ⟨h', h'meas, h'mem, h'rep, h'orth⟩ :=
    exists_memLp_two_representer_of_finite_norm μ hμ h hh
  refine ⟨fun x => ENNReal.ofReal
      (Real.exp (h' x - (∫ y, (h' y) ^ 2 ∂μ) / 2)), ?_, ?_, ?_⟩
  · exact ENNReal.measurable_ofReal.comp
      (Real.measurable_exp.comp (h'meas.sub measurable_const))
  · intro x
    exact ENNReal.ofReal_ne_zero_iff.mpr (Real.exp_pos _)
  · exact map_add_eq_withDensity_of_memLp_representer μ hμ h h' h'meas h'mem h'rep h'orth
