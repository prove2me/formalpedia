-- Prove2me | solution 1 for HairerSPDE.cameron_martin
-- status  : ACCEPTED   (prove)
-- author  : @Lucas
-- created : 2026-09-18T21:40:29.592108+00:00
-- url     : https://prove2.me/submissions/dc850e21-261e-4b1f-b2c7-5afbfb47e09d

import Mathlib
import Definitions.Def_HairerSPDE_CameronMartin
import Theorems.Thm_HairerSPDE_cameronMartinNorm_ne_top_iff_forall_submodule
import Theorems.Thm_HairerSPDE_map_add_exists_pos_withDensity_of_finite_norm

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology

open HairerSPDE in
theorem solution {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B] [MeasurableSpace B]
    [BorelSpace B] [CompleteSpace B] [SecondCountableTopology B]
    (μ : Measure B) [IsGaussian μ] (hμ : μ[id] = 0) (h : B) :
    μ.map (fun x ↦ x + h) ≪ μ ↔ cameronMartinNorm μ h ≠ ∞ := by
  constructor
  · intro hac
    rw [cameronMartinNorm_ne_top_iff_forall_submodule μ hμ h]
    intro V hV hV1
    by_contra hnot
    -- `Vᶜ` is `μ`-null, hence null for the translated measure
    have hcompl : μ (V : Set B)ᶜ = 0 := by
      have : μ Set.univ = 1 := measure_univ
      have hle : μ (V : Set B) ≤ μ Set.univ := measure_mono (Set.subset_univ _)
      have := measure_compl hV (by rw [hV1]; exact ENNReal.one_ne_top)
      rw [this, hV1, measure_univ, tsub_self]
    have hnull := hac hcompl
    -- but the preimage of `Vᶜ` under the translation contains `V`, which has full measure
    have hmeas : Measurable (fun x : B => x + h) := measurable_id.add_const h
    have hpre : (μ.map (fun x : B => x + h)) (V : Set B)ᶜ
        = μ ((fun x : B => x + h) ⁻¹' (V : Set B)ᶜ) :=
      Measure.map_apply hmeas hV.compl
    have hsub : (V : Set B) ⊆ (fun x : B => x + h) ⁻¹' (V : Set B)ᶜ := by
      intro x hx
      simp only [Set.mem_preimage, Set.mem_compl_iff, SetLike.mem_coe]
      intro hxh
      exact hnot (by simpa using V.sub_mem hxh hx)
    have : (1 : ℝ≥0∞) ≤ 0 := by
      calc (1 : ℝ≥0∞) = μ (V : Set B) := hV1.symm
        _ ≤ μ ((fun x : B => x + h) ⁻¹' (V : Set B)ᶜ) := measure_mono hsub
        _ = (μ.map (fun x : B => x + h)) (V : Set B)ᶜ := hpre.symm
        _ = 0 := hnull
    exact absurd this (by simp)
  · intro hh
    obtain ⟨f, _hf, _hfne, hfeq⟩ :=
      map_add_exists_pos_withDensity_of_finite_norm μ hμ h hh
    rw [hfeq]
    exact withDensity_absolutelyContinuous μ f
