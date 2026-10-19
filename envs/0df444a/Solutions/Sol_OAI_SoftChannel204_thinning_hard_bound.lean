-- Prove2me | solution 1 for OAI.SoftChannel204.thinning_hard_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T15:49:10.92097+00:00
-- url     : https://prove2.me/submissions/7afcca3b-b268-4e41-a0ce-e0ee24cf0d62

-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/SoftChannel/Thinning.lean:L174-L231
-- (upload_full_project.md Phase 4): solution for node OAI.SoftChannel204.thinning_hard_bound. The node keeps its source
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

-- ---- from OAI.InformationTheory.SoftChannel.Thinning ----
namespace OAI

section

noncomputable section
open Set
namespace SoftChannel204

theorem thinningPolynomial_pos (t u : ℝ) (hu0 : 0 ≤ u) (hu1 : u ≤ 1)
    (ht0 : 0 ≤ t) (htu : t * (1 + u) ≤ 1) : 0 < thinningPolynomial t u := by
  let a := 12 - 8 * u + 8 * u ^ 2 - 6 * u ^ 3
  let b := 3 * u ^ 2 - u - 8
  let c := u * (3 - u) * (2 - 3 * u ^ 2)
  have hc : -u * (1 + u) ≤ c := by
    have h : 0 ≤ u * (1 - u) * (7 + 6 * u - 3 * u ^ 2) := by
      have : u ^ 2 ≤ u := by nlinarith
      apply mul_nonneg (mul_nonneg hu0 (sub_nonneg.mpr hu1))
      nlinarith
    dsimp [c]
    nlinarith
  have hct : -u ≤ c * t := by
    calc
      -u ≤ -u * (t * (1 + u)) := by nlinarith
      _ = (-u * (1 + u)) * t := by ring
      _ ≤ c * t := mul_le_mul_of_nonneg_right hc ht0
  have hp : 2 + b * t + (a - u) * t ^ 2 ≤ thinningPolynomial t u := by
    have h := mul_nonneg (show 0 ≤ c * t + u by linarith) (sq_nonneg t)
    dsimp [thinningPolynomial, a, b, c] at *
    nlinarith
  have hd : 4 ≤ 8 * (a - u) - b ^ 2 := by
    have h : 0 ≤ (1 - u) * (2 * (5 * u - 3) ^ 2 + u ^ 2 * (1 + 9 * u) + 10) :=
      mul_nonneg (sub_nonneg.mpr hu1) (by positivity)
    dsimp [a, b]
    nlinarith
  have hd' := mul_le_mul_of_nonneg_right hd (sq_nonneg t)
  by_cases ht : t = 0
  · subst t
    norm_num [thinningPolynomial]
  · have hs : 0 < t ^ 2 := sq_pos_of_ne_zero ht
    nlinarith [sq_nonneg (4 + b * t)]

theorem clipKernel_of_le {β v : ℝ} (h : v ≤ β) : clipKernel β v = 0 := by
  simp [clipKernel, max_eq_right (sub_nonpos.mpr h)]

theorem clipKernel_eq {β v : ℝ} (h : β ≤ v) :
    clipKernel β v = (v - β) / v ^ 2 := by
  rw [clipKernel, max_eq_left (sub_nonneg.mpr h)]

theorem thinning_endpoint_algebra {t u : ℝ} (ht0 : 0 ≤ t) (hu0 : 0 < u)
    (hu1 : u ≤ 1) (htu : t * (1 + u) ≤ 1) :
    let b := t * u
    let x := 3 * b / (4 - b)
    ((1 + x) * ((u - b) / u ^ 2) - x * (1 - b)) *
      ((4 * x + (1 - x) * u) / ((1 - x) * (1 + x))) ≤ 3 / 2 := by
  dsimp only
  have ht : t * u < 1 := by
    by_cases he : t = 0
    · simp [he]
    · have : 0 < t := lt_of_le_of_ne ht0 (Ne.symm he)
      nlinarith
  have h4 : 4 - t * u ≠ 0 := by linarith
  have h1 : 1 - t * u ≠ 0 := by linarith
  have h2 : 2 + t * u ≠ 0 := by positivity
  have hp := (thinningPolynomial_pos t u hu0.le hu1 ht0 htu).le
  have hd : 0 < 2 * (1 - t * u) * (2 + t * u) := by positivity
  have hf : 1 - 3 * (t * u) / (4 - t * u) ≠ 0 := by
    intro he
    have he' := (div_eq_iff h4).mp (show 3 * (t * u) / (4 - t * u) = 1 by linarith)
    nlinarith
  have hf' : 1 + 3 * (t * u) / (4 - t * u) ≠ 0 := by
    have : 0 ≤ 3 * (t * u) / (4 - t * u) := div_nonneg (by positivity) (by linarith)
    positivity
  have hid : 3 / 2 -
      ((1 + 3 * (t * u) / (4 - t * u)) * ((u - t * u) / u ^ 2) -
        3 * (t * u) / (4 - t * u) * (1 - t * u)) *
        ((4 * (3 * (t * u) / (4 - t * u)) +
          (1 - 3 * (t * u) / (4 - t * u)) * u) /
          ((1 - 3 * (t * u) / (4 - t * u)) * (1 + 3 * (t * u) / (4 - t * u)))) =
      thinningPolynomial t u / (2 * (1 - t * u) * (2 + t * u)) := by
    unfold thinningPolynomial
    have hden : 16 - t * u * 8 - t ^ 2 * u ^ 2 * 8 ≠ 0 := by
      have he : 16 - t * u * 8 - t ^ 2 * u ^ 2 * 8 =
          8 * (1 - t * u) * (2 + t * u) := by ring
      rw [he]
      exact mul_ne_zero (mul_ne_zero (by norm_num) h1) h2
    field_simp [hu0.ne', h4, hf, hf', h1, h2, hden]
    ring_nf
    field_simp [hden]
    ring
  have hnonneg := div_nonneg hp hd.le
  rw [← hid] at hnonneg
  linarith

theorem thinning_hard_bound {x u β : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1)
    (hu0 : 0 < u) (hu1 : u ≤ 1) (hβ1 : β ≤ 1)
    (hcut : 4 * x / (3 + x) ≤ β) (hh : 1 - β < clipKernel β u) :
    ((1 + x) * clipKernel β u - x * (1 - β)) *
      ((4 * x + (1 - x) * u) / ((1 - x) * (1 + x))) ≤ 3 / 2 := by
  let b : ℝ := 4 * x / (3 + x)
  have hb0 : 0 ≤ b := div_nonneg (by positivity) (by positivity)
  have hbβ : b ≤ β := hcut
  have hβ0 : 0 ≤ β := hb0.trans hbβ
  have hbu : β < u := by
    by_contra hn
    rw [clipKernel_of_le (le_of_not_gt hn)] at hh
    linarith
  have hk : clipKernel β u * u ^ 2 = u - β := by
    rw [clipKernel_eq hbu.le, div_mul_cancel₀ _ (pow_ne_zero _ hu0.ne')]
  have hp : 0 < (1 - u) * (u - β * (1 + u)) := by
    have hm := mul_lt_mul_of_pos_right hh (sq_pos_of_pos hu0)
    rw [hk] at hm
    nlinarith
  have hcore : β * (1 + u) < u := by
    by_contra hn
    have := mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hu1)
      (show u - β * (1 + u) ≤ 0 by linarith)
    linarith
  have hbcore : b * (1 + u) ≤ u :=
    (mul_le_mul_of_nonneg_right hbβ (by positivity)).trans hcore.le
  have hb1 : b < 1 := by nlinarith
  let t := b / u
  have ht0 : 0 ≤ t := div_nonneg hb0 hu0.le
  have htu : t * u = b := div_mul_cancel₀ _ hu0.ne'
  have ht : t * (1 + u) ≤ 1 := by
    dsimp [t]
    rw [div_mul_eq_mul_div, div_le_iff₀ hu0]
    simpa using hbcore
  have h4 : 4 - b ≠ 0 := by linarith
  have hbx : 3 * b / (4 - b) = x := by
    apply (div_eq_iff h4).mpr
    dsimp [b]
    field_simp
    ring
  have hend := thinning_endpoint_algebra ht0 hu0 hu1 ht
  dsimp only at hend
  rw [htu, hbx] at hend
  have hcoeff : 0 ≤ (1 + x) / u ^ 2 - x := by
    have hsq : u ^ 2 ≤ 1 := by nlinarith
    have hle : x ≤ (1 + x) / u ^ 2 := by
      apply (le_div_iff₀ (sq_pos_of_pos hu0)).mpr
      nlinarith [mul_le_mul_of_nonneg_left hsq hx0]
    linarith
  have hcomp : (1 + x) * clipKernel β u - x * (1 - β) ≤
      (1 + x) * ((u - b) / u ^ 2) - x * (1 - b) := by
    rw [clipKernel_eq hbu.le]
    have h := mul_nonneg (sub_nonneg.mpr hbβ) hcoeff
    simp only [div_eq_mul_inv] at *
    nlinarith
  have hfac : 0 ≤ (4 * x + (1 - x) * u) / ((1 - x) * (1 + x)) := by
    apply div_nonneg <;> positivity
  exact (mul_le_mul_of_nonneg_right hcomp hfac).trans hend

open MeasureTheory

end SoftChannel204
end
end

end OAI

-- ---- platform node ----
open OAI OAI.SoftChannel204
open Set


theorem solution : type_of% @_root_.OAI.SoftChannel204.thinning_hard_bound := @_root_.OAI.SoftChannel204.thinning_hard_bound
