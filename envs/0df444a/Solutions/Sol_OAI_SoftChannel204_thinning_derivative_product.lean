-- Prove2me | solution 1 for OAI.SoftChannel204.thinning_derivative_product
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T15:50:58.658989+00:00
-- url     : https://prove2.me/submissions/18f0cbaa-c64b-4640-9ed0-07c1538cdb31

-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/SoftChannel/Thinning.lean:L233-L316
-- (upload_full_project.md Phase 4): solution for node OAI.SoftChannel204.thinning_derivative_product. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_SoftChannel204
import Definitions.Def_OAI_Combinatorics_GotsmanLinial_Model
import Definitions.Def_OAI_Combinatorics_GotsmanLinial_Statement
import Definitions.Def_OAI_InformationTheory_BooleanNoise_Model
import Definitions.Def_OAI_InformationTheory_BooleanNoise_Basic__SoftChannel204
import Definitions.Def_OAI_InformationTheory_BooleanNoise_EntropyScalars__SoftChannel204
import Definitions.Def_OAI_InformationTheory_BooleanNoise_CurvatureCertificates__SoftChannel204
import Definitions.Def_OAI_InformationTheory_BooleanNoise_InverseScalars__SoftChannel204
import Definitions.Def_OAI_InformationTheory_BooleanNoise_EntropySeries__SoftChannel204
import Definitions.Def_OAI_InformationTheory_BooleanNoise_EntropyBounds__SoftChannel204
import Definitions.Def_OAI_InformationTheory_BooleanNoise_MediumCurvature__SoftChannel204
import Definitions.Def_OAI_InformationTheory_BooleanNoise_CurvatureBounds__SoftChannel204
import Definitions.Def_OAI_InformationTheory_BooleanNoise_LRegularity__SoftChannel204
import Definitions.Def_OAI_InformationTheory_BooleanNoise_FiniteNoise__SoftChannel204
import Definitions.Def_OAI_InformationTheory_BooleanNoise_Rearrangement__SoftChannel204
import Definitions.Def_OAI_InformationTheory_BooleanNoise_SemigroupFlow__SoftChannel204
import Definitions.Def_OAI_InformationTheory_BooleanNoise_CubeSplits__SoftChannel204
import Definitions.Def_OAI_InformationTheory_BooleanNoise_PairEntropy__SoftChannel204
import Definitions.Def_OAI_InformationTheory_BooleanNoise_LambdaScalars__SoftChannel204
import Definitions.Def_OAI_InformationTheory_BooleanNoise_JensenGaps__SoftChannel204
import Definitions.Def_OAI_InformationTheory_BooleanNoise_CubeVariance__SoftChannel204
import Definitions.Def_OAI_InformationTheory_BooleanNoise_NormalizedPair__SoftChannel204
import Definitions.Def_OAI_InformationTheory_BooleanNoise_PerspectiveLogTrapezoid__SoftChannel204
import Definitions.Def_OAI_InformationTheory_BooleanNoise_PerspectiveCalculus__SoftChannel204
import Definitions.Def_OAI_InformationTheory_BooleanNoise_PerspectiveInequality__SoftChannel204
import Definitions.Def_OAI_InformationTheory_BooleanNoise_Comparison__SoftChannel204
import Definitions.Def_OAI_InformationTheory_BooleanNoise_Statement__SoftChannel204
import Definitions.Def_OAI_InformationTheory_BooleanNoise_FiniteDistribution__SoftChannel204
import Definitions.Def_OAI_InformationTheory_BooleanNoise_Attainment__SoftChannel204
import Definitions.Def_OAI_InformationTheory_SoftChannel_Canonical
import Definitions.Def_OAI_InformationTheory_SoftChannel_Thinning
import Theorems.Thm_OAI_SoftChannel204_thinning_hard_bound

-- ---- from OAI.InformationTheory.SoftChannel.Thinning ----
namespace OAI

section

noncomputable section
open Set
namespace SoftChannel204

theorem clipKernel_nonneg (β v : ℝ) : 0 ≤ clipKernel β v :=
  div_nonneg (le_max_right _ _) (sq_nonneg _)

theorem clipKernel_of_le {β v : ℝ} (h : v ≤ β) : clipKernel β v = 0 := by
  simp [clipKernel, max_eq_right (sub_nonpos.mpr h)]

theorem clipKernel_eq {β v : ℝ} (h : β ≤ v) :
    clipKernel β v = (v - β) / v ^ 2 := by
  rw [clipKernel, max_eq_left (sub_nonneg.mpr h)]

theorem clipKernel_min {β u v : ℝ} (hβ0 : 0 ≤ β) (hu0 : 0 < u)
    (huv : u ≤ v) (hv1 : v ≤ 1) :
    min (clipKernel β u) (1 - β) ≤ clipKernel β v := by
  by_cases huβ : u ≤ β
  · rw [clipKernel_of_le huβ]
    exact (min_le_left _ _).trans (clipKernel_nonneg _ _)
  have hβu : β < u := lt_of_not_ge huβ
  have hv0 : 0 < v := hu0.trans_le huv
  have hβv : β ≤ v := hβu.le.trans huv
  have hc : ConcaveOn ℝ (Ici (0 : ℝ)) (fun t => t - β * t ^ 2) := by
    convert! (concaveOn_id (convex_Ici (0 : ℝ))).sub
      ((convexOn_pow (𝕜 := ℝ) 2).smul hβ0) using 1
  have hi : (1 / v : ℝ) ∈ Icc 1 (1 / u) := by
    constructor
    · exact (le_div_iff₀ hv0).mpr (by simpa using hv1)
    · exact one_div_le_one_div_of_le hu0 huv
  have h := hc.min_le_of_mem_Icc (show (1 : ℝ) ∈ Ici 0 by norm_num)
    (show 1 / u ∈ Ici (0 : ℝ) from (one_div_pos.mpr hu0).le) hi
  have he (w : ℝ) (hw : w ≠ 0) :
      1 / w - β * (1 / w) ^ 2 = (w - β) / w ^ 2 := by
    field_simp
  simp only [one_pow, mul_one] at h
  rw [he u hu0.ne', he v hv0.ne', min_comm] at h
  rwa [clipKernel_eq hβu.le, clipKernel_eq hβv]

theorem thinning_derivative_product {x a s β : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1)
    (ha1 : 1 ≤ a) (hap : a ≤ 1 + x) (hs0 : 0 ≤ s)
    (hsg : s < (1 - x) / (1 + x)) (hβ1 : β ≤ 1)
    (hcut : 4 * x / (3 + x) ≤ β) :
    let u := 2 - a * (1 + s)
    let v := u + s
    (a * clipKernel β u - (a - 1) * clipKernel β v) *
      ((1 + x) / (1 - x) - s) ≤ 3 / 2 := by
  let u := 2 - a * (1 + s)
  let v := u + s
  let Y := (1 + x) / (1 - x) - s
  change (a * clipKernel β u - (a - 1) * clipKernel β v) * Y ≤ 3 / 2
  have hp : 0 < 1 + x := by positivity
  have hσ : 0 < 1 - x := by linarith
  have ha : 0 < a := by linarith
  have hs : (1 + x) * s < 1 - x := by
    have := (lt_div_iff₀ hp).mp hsg
    nlinarith
  have hu0 : 0 < u := by
    have hh := mul_le_mul_of_nonneg_right hap (show 0 ≤ 1 + s by positivity)
    dsimp [u]
    nlinarith
  have huv : u ≤ v := by dsimp [v]; linarith
  have hv1 : v ≤ 1 := by
    have hh := mul_le_mul_of_nonneg_right ha1 (show 0 ≤ 1 + s by positivity)
    dsimp [v, u]
    nlinarith
  have hu1 : u ≤ 1 := huv.trans hv1
  have hs1 : s < 1 := by nlinarith [mul_nonneg hx0 hs0]
  have hratio : 1 ≤ (1 + x) / (1 - x) := by
    apply (le_div_iff₀ hσ).mpr
    linarith
  have hY : 0 < Y := by dsimp [Y]; linarith
  have hb0 : 0 ≤ β :=
    (div_nonneg (show 0 ≤ 4 * x by positivity) (show 0 ≤ 3 + x by positivity)).trans hcut
  have hc0 : 0 ≤ 1 - β := by linarith
  have hmin := clipKernel_min hb0 hu0 huv hv1
  by_cases heasy : clipKernel β u ≤ 1 - β
  · rw [min_eq_left heasy] at hmin
    have hD : a * clipKernel β u - (a - 1) * clipKernel β v ≤ 1 - β := by
      have := mul_nonneg (show 0 ≤ a - 1 by linarith) (sub_nonneg.mpr hmin)
      nlinarith
    have hc : (1 - β) * (2 * (1 + x)) ≤ 3 * (1 - x) := by
      have hb := (div_le_iff₀ (show 0 < 3 + x by positivity)).mp hcut
      have hh := mul_le_mul_of_nonneg_left
        (show 2 * (1 + x) ≤ 3 + x by linarith) hc0
      nlinarith
    calc
      _ ≤ (1 - β) * Y := mul_le_mul_of_nonneg_right hD hY.le
      _ ≤ (1 - β) * ((1 + x) / (1 - x)) :=
        mul_le_mul_of_nonneg_left (by dsimp [Y]; linarith) hc0
      _ = ((1 - β) * (1 + x)) / (1 - x) := by ring
      _ ≤ 3 / 2 := (div_le_iff₀ hσ).mpr (by nlinarith)
  · have hhard : 1 - β < clipKernel β u := lt_of_not_ge heasy
    rw [min_eq_right hhard.le] at hmin
    have hD : a * clipKernel β u - (a - 1) * clipKernel β v ≤
        a * (clipKernel β u - (1 - β)) + (1 - β) := by
      have := mul_nonneg (show 0 ≤ a - 1 by linarith) (sub_nonneg.mpr hmin)
      nlinarith
    have hfirst : a * (clipKernel β u - (1 - β)) + (1 - β) ≤
        (1 + x) * (clipKernel β u - (1 - β)) + (1 - β) := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hap) (sub_nonneg.mpr hhard.le)]
    have hid : Y = 2 / (1 - x) - (2 - u) / a := by
      dsimp [Y, u]
      field_simp
      ring
    have hidp : 2 / (1 - x) - (2 - u) / (1 + x) =
        (4 * x + (1 - x) * u) / ((1 - x) * (1 + x)) := by
      field_simp
      ring
    have hYle : Y ≤ (4 * x + (1 - x) * u) / ((1 - x) * (1 + x)) := by
      rw [hid, ← hidp]
      exact sub_le_sub_left (div_le_div_of_nonneg_left (by linarith) ha hap) _
    have hbound := thinning_hard_bound hx0 hx1 hu0 hu1 hβ1 hcut hhard
    calc
      _ ≤ (a * (clipKernel β u - (1 - β)) + (1 - β)) * Y :=
        mul_le_mul_of_nonneg_right hD hY.le
      _ ≤ ((1 + x) * (clipKernel β u - (1 - β)) + (1 - β)) *
          ((4 * x + (1 - x) * u) / ((1 - x) * (1 + x))) :=
        mul_le_mul hfirst hYle hY.le
          (add_nonneg (mul_nonneg hp.le (sub_nonneg.mpr hhard.le)) hc0)
      _ = ((1 + x) * clipKernel β u - x * (1 - β)) *
          ((4 * x + (1 - x) * u) / ((1 - x) * (1 + x))) := by ring
      _ ≤ 3 / 2 := hbound

open MeasureTheory

end SoftChannel204
end
end

end OAI

-- ---- platform node ----
open OAI OAI.SoftChannel204
open Set


theorem solution : type_of% @_root_.OAI.SoftChannel204.thinning_derivative_product := @_root_.OAI.SoftChannel204.thinning_derivative_product
