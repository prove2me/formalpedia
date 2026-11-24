-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.p2m87_qpos_interval_density_halfline_add_split
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T02:03:21.915975+00:00
-- url     : https://prove2.me/submissions/ba651915-c414-4388-a3c7-34534cb393a4

import Mathlib
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_B
import Theorems.Thm_Kyprianou_Ch08_StageB_source_result81_exponent_quadratic_upper
import Theorems.Thm_Kyprianou_Ch08_StageB_source_result81_scale_positive_from_quadratic
import Theorems.Thm_Kyprianou_Ch08_StageB_p2m88_source_killed_density_measurable
import Theorems.Thm_Kyprianou_Ch08_StageB_p2m87_qpos_halfline_density_nonneg
import Theorems.Thm_Kyprianou_Ch08_StageB_p2m87_qpos_interval_density_nonneg
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal
open Kyprianou.Ch08
open Kyprianou.Ch08.StageB

theorem p2m87_qpos_interval_density_halfline_add_split_core :
    ∀ (Ω : Type) [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (D : SpectrallyNegativeModel Ω P) (ψ : ℝ → ℝ)
    (W : ℝ → ℝ → ℝ),
    IsLaplaceExponent (SpectrallyNegativeModel.toData P D) ψ →
    HasSourceScaleFamily ψ W →
    ∀ (q a x : ℝ), 0 < q → 0 < a → 0 ≤ x → x ≤ a →
      ∀ (A : Set ℝ), MeasurableSet A →
        ((volume.restrict (Set.Ici (0 : ℝ))).withDensity
          (fun y : ℝ => ENNReal.ofReal
            (killedHalflineDensity ψ q (W q) x y))) A =
        ((volume.restrict (Set.Icc 0 a)).withDensity
          (fun y : ℝ => ENNReal.ofReal
            (killedIntervalDensity (W q) a x y))) A +
        ENNReal.ofReal (W q x / W q a) *
          ((volume.restrict (Set.Ici (0 : ℝ))).withDensity
            (fun y : ℝ => ENNReal.ofReal
              (killedHalflineDensity ψ q (W q) a y))) A := by
  intro Ω mΩ P hP D ψ W hψ hW q a x hq ha hx hxa A hA
  have hWq : IsQScale ψ q (W q) := hW q (le_of_lt hq)
  have hneg : ∀ z : ℝ, z < 0 → W q z = 0 := hWq.2.1
  have hnonneg : ∀ z : ℝ, 0 ≤ W q z := hWq.2.2.1
  obtain ⟨K, hK, hg⟩ := source_result81_exponent_quadratic_upper Ω P D ψ hψ
  have hWa : 0 < W q a := source_result81_scale_positive_from_quadratic ψ q (W q) hWq K hK hg a ha
  let fx : ℝ → ENNReal := fun y => ENNReal.ofReal (killedHalflineDensity ψ q (W q) x y)
  let fi : ℝ → ENNReal := fun y => ENNReal.ofReal (killedIntervalDensity (W q) a x y)
  let fa : ℝ → ENNReal := fun y => ENNReal.ofReal (killedHalflineDensity ψ q (W q) a y)
  let r : ENNReal := ENNReal.ofReal (W q x / W q a)
  have hratio : 0 ≤ W q x / W q a := div_nonneg (hnonneg x) (le_of_lt hWa)
  have hfa : Measurable fa := by
    simpa [fa] using p2m88_source_killed_density_measurable ψ W hW q (le_of_lt hq) a
  have hgmeas : Measurable ((Ici 0).indicator (fun y => r * fa y)) :=
    (hfa.const_mul r).indicator measurableSet_Ici
  have hpoint : ∀ y : ℝ, (Ici 0).indicator fx y =
      (Icc 0 a).indicator fi y + (Ici 0).indicator (fun z => r * fa z) y := by
    intro y
    by_cases hy : 0 ≤ y
    · by_cases hya : y ≤ a
      · have heq : killedHalflineDensity ψ q (W q) x y = killedIntervalDensity (W q) a x y + (W q x / W q a) * killedHalflineDensity ψ q (W q) a y := by
          unfold killedHalflineDensity killedIntervalDensity
          field_simp [hWa.ne']
          ring
        have hki := p2m87_qpos_interval_density_nonneg Ω P D ψ W hψ hW q a x y hq ha hx hxa hy hya
        have hka := p2m87_qpos_halfline_density_nonneg Ω P D ψ W hψ hW q a y hq (le_of_lt ha) hy
        have hs : ENNReal.ofReal (killedHalflineDensity ψ q (W q) x y) = ENNReal.ofReal (killedIntervalDensity (W q) a x y) + r * ENNReal.ofReal (killedHalflineDensity ψ q (W q) a y) := by
          rw [heq, ENNReal.ofReal_add hki (mul_nonneg hratio hka), ENNReal.ofReal_mul hratio]
        simpa [fx, fi, fa, r, hy, hya] using hs
      · have heq : killedHalflineDensity ψ q (W q) x y = (W q x / W q a) * killedHalflineDensity ψ q (W q) a y := by
          unfold killedHalflineDensity
          rw [hneg (a - y) (by linarith), hneg (x - y) (by linarith)]
          field_simp [hWa.ne']
          ring
        have hs : ENNReal.ofReal (killedHalflineDensity ψ q (W q) x y) = r * ENNReal.ofReal (killedHalflineDensity ψ q (W q) a y) := by
          rw [heq, ENNReal.ofReal_mul hratio]
        simpa [fx, fi, fa, r, hy, hya, lt_of_not_ge hya] using hs
    · simp [fx, fi, fa, hy]
  have hsmul : (Ici 0).indicator (fun y => r * fa y) = r • (Ici 0).indicator fa := by
    funext y
    by_cases hy : y ∈ Ici (0 : ℝ) <;> simp [hy]
  have hcongr : volume.withDensity ((Ici 0).indicator fx) =
      volume.withDensity ((Icc 0 a).indicator fi + (Ici 0).indicator (fun y => r * fa y)) := by
    apply withDensity_congr_ae
    filter_upwards with y
    exact hpoint y
  have hsub : Icc 0 a ⊆ Ici (0 : ℝ) := by intro z hz; exact hz.1
  have hmeasure : (volume.restrict (Ici 0)).withDensity fx =
      (volume.restrict (Icc 0 a)).withDensity fi + r • (volume.restrict (Ici 0)).withDensity fa := by
    calc
      (volume.restrict (Ici 0)).withDensity fx = volume.withDensity ((Ici 0).indicator fx) :=
        (withDensity_indicator measurableSet_Ici fx).symm
      _ = volume.withDensity ((Icc 0 a).indicator fi + (Ici 0).indicator (fun y => r * fa y)) := hcongr
      _ = volume.withDensity ((Icc 0 a).indicator fi) + volume.withDensity ((Ici 0).indicator (fun y => r * fa y)) :=
        withDensity_add_right ((Icc 0 a).indicator fi) hgmeas
      _ = volume.withDensity ((Icc 0 a).indicator fi) + volume.withDensity (r • (Ici 0).indicator fa) := by rw [hsmul]
      _ = (volume.restrict (Icc 0 a)).withDensity fi + r • volume.withDensity ((Ici 0).indicator fa) := by
        rw [withDensity_indicator measurableSet_Icc, withDensity_smul' r ((Ici 0).indicator fa) ENNReal.ofReal_ne_top]
      _ = (volume.restrict (Icc 0 a)).withDensity fi + r • (volume.restrict (Ici 0)).withDensity fa := by
        rw [withDensity_indicator measurableSet_Ici]
  simpa [fx, fi, fa, r] using congrArg (fun μ : Measure ℝ => μ A) hmeasure

theorem solution :
    ∀ (Ω : Type) [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (D : SpectrallyNegativeModel Ω P) (ψ : ℝ → ℝ) (W : ℝ → ℝ → ℝ),
    IsLaplaceExponent (SpectrallyNegativeModel.toData P D) ψ →
    HasSourceScaleFamily ψ W →
    ∀ (q a x : ℝ), 0 < q → 0 < a → 0 ≤ x → x ≤ a →
      ∀ (A : Set ℝ), MeasurableSet A →
        ((volume.restrict (Set.Ici (0 : ℝ))).withDensity
          (fun y : ℝ => ENNReal.ofReal
            (killedHalflineDensity ψ q (W q) x y))) A =
        ((volume.restrict (Set.Icc 0 a)).withDensity
          (fun y : ℝ => ENNReal.ofReal
            (killedIntervalDensity (W q) a x y))) A +
        ENNReal.ofReal (W q x / W q a) *
          ((volume.restrict (Set.Ici (0 : ℝ))).withDensity
            (fun y : ℝ => ENNReal.ofReal
              (killedHalflineDensity ψ q (W q) a y))) A := by
  intro Ω mΩ P hP D ψ W hψ hW q a x hq ha hx hxa A hA
  exact p2m87_qpos_interval_density_halfline_add_split_core Ω P D ψ W hψ hW q a x hq ha hx hxa A hA
