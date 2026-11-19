-- Prove2me | solution 1 for Kyprianou.Ch01.compoundPoissonEventualLinearUpperBoundAE
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T13:41:56.071556+00:00
-- url     : https://prove2.me/submissions/fe2181f3-3554-40aa-924f-81735daab1a5

import Mathlib
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
import Theorems.Thm_Kyprianou_Ch01_compoundPoissonFiniteOffspringMeanRatioConvergesAE
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (Q : Measure Ω) [IsProbabilityMeasure Q]
    (rate : ℝ≥0) (hrate : 0 < rate)
    (offspring : PMF ℕ)
    (hFiniteMean : Summable (fun k : ℕ => (offspring k).toReal * (k : ℝ)))
    (arrival marks : ℕ → Ω → ℝ)
    (jumpLaw : Measure ℝ) [IsProbabilityMeasure jumpLaw]
    (hdriver : IsCompoundPoissonDriver arrival marks rate jumpLaw Q)
    (hSupport : jumpLaw {x : ℝ | ∃ k : ℕ, x = (k : ℝ) - 1} = 1)
    (hJumpMass : ∀ k : ℕ,
      jumpLaw ({((k : ℝ) - 1)} : Set ℝ) = offspring k) :
    ∀ᵐ ω ∂Q, ∃ (T : ℝ≥0) (K : ℝ), 0 ≤ K ∧
      ∀ t : ℝ≥0, T ≤ t →
        ProbabilityTheory.compoundPoisson 0 arrival marks (t : ℝ) ω ≤
          K * (1 + (t : ℝ)) := by
  filter_upwards
    [Kyprianou.Ch01.compoundPoissonFiniteOffspringMeanRatioConvergesAE
      Q rate hrate offspring hFiniteMean arrival marks jumpLaw hdriver
      hSupport hJumpMass] with ω hlimit
  obtain ⟨L, hL⟩ := hlimit
  have he : ∀ᶠ t : ℝ≥0 in atTop,
      ProbabilityTheory.compoundPoisson 0 arrival marks (t : ℝ) ω /
        (1 + (t : ℝ)) < L + 1 :=
    hL.eventually_lt_const (by linarith)
  obtain ⟨T, hT⟩ := Filter.eventually_atTop.1 he
  let K : ℝ := max (L + 1) 0
  refine ⟨T, K, le_max_right _ _, ?_⟩
  intro t ht
  have hratio := hT t ht
  have hden : 0 < 1 + (t : ℝ) := by positivity
  have hp : ProbabilityTheory.compoundPoisson 0 arrival marks (t : ℝ) ω <
      (L + 1) * (1 + (t : ℝ)) :=
    (div_lt_iff₀ hden).mp hratio
  exact (le_of_lt hp).trans
    (mul_le_mul_of_nonneg_right (le_max_left _ _) (le_of_lt hden))
