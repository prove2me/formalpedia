-- Prove2me | solution 1 for HairerSPDE.map_add_null_iff
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-14T11:36:06.229337+00:00
-- url     : https://prove2.me/submissions/6524d8af-3bc2-4658-86e1-bd04329897a7

import Mathlib
import Definitions.Def_HairerSPDE_CameronMartin
import Theorems.Thm_HairerSPDE_map_add_exists_pos_withDensity_of_finite_norm

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
    ∀ A : Set B, MeasurableSet A → ((μ.map (fun x : B => x + h)) A = 0 ↔ μ A = 0) := by
  obtain ⟨f, hf_meas, hf_ne, hmap⟩ :=
    map_add_exists_pos_withDensity_of_finite_norm μ hμ h hh
  intro A hA
  rw [hmap, withDensity_apply f hA, lintegral_eq_zero_iff' hf_meas.aemeasurable]
  rw [← Measure.restrict_eq_zero]
  constructor
  · intro hf0
    have h1 : (μ.restrict A) {a : B | ¬ f a = 0} = 0 := ae_iff.mp hf0
    have huniv : {a : B | ¬ f a = 0} = Set.univ := by
      ext x
      simp [hf_ne x]
    rw [huniv] at h1
    exact Measure.measure_univ_eq_zero.mp h1
  · intro h0
    simp [h0]
    exact Filter.eventually_bot
