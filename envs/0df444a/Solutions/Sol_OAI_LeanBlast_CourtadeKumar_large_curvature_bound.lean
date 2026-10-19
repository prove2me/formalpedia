-- Prove2me | solution 1 for OAI.LeanBlast.CourtadeKumar.large_curvature_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T12:17:27.984987+00:00
-- url     : https://prove2.me/submissions/122edd15-ea12-4b50-be36-121155903ce5

-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/BooleanNoise/LargeCurvature.lean:L62-L132
-- (upload_full_project.md Phase 4): solution for node OAI.LeanBlast.CourtadeKumar.large_curvature_bound. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_CourtadeKumar
import Definitions.Def_OAI_Combinatorics_GotsmanLinial_Model__CourtadeKumar
import Definitions.Def_OAI_Combinatorics_GotsmanLinial_Statement__CourtadeKumar
import Definitions.Def_OAI_InformationTheory_BooleanNoise_Basic
import Definitions.Def_OAI_InformationTheory_BooleanNoise_FiniteNoise
import Definitions.Def_OAI_InformationTheory_BooleanNoise_Statement
import Definitions.Def_OAI_InformationTheory_BooleanNoise_EntropyScalars
import Definitions.Def_OAI_InformationTheory_BooleanNoise_FiniteDistribution
import Definitions.Def_OAI_InformationTheory_BooleanNoise_Attainment
import Definitions.Def_OAI_InformationTheory_BooleanNoise_Rearrangement
import Definitions.Def_OAI_InformationTheory_BooleanNoise_CurvatureCertificates
import Definitions.Def_OAI_InformationTheory_BooleanNoise_ComparisonEstimates
import Definitions.Def_OAI_InformationTheory_BooleanNoise_InverseScalars
import Definitions.Def_OAI_InformationTheory_BooleanNoise_EntropySeries
import Definitions.Def_OAI_InformationTheory_BooleanNoise_EntropyBounds
import Definitions.Def_OAI_InformationTheory_BooleanNoise_MediumCurvature

-- ---- from OAI.InformationTheory.BooleanNoise.EntropyScalars ----
namespace OAI

noncomputable section

open Set Filter
open scoped Topology

namespace LeanBlast.CourtadeKumar

theorem entropy_nonneg {v : ℝ} (hv : v ∈ Icc (-1) 1) : 0 ≤ entropy v := by
  rw [entropy_eq_binEntropy]
  exact Real.binEntropy_nonneg (by linarith [hv.1]) (by linarith [hv.2])

theorem artanh_eq_log_sub {v : ℝ} (hv : v ∈ Ioo (-1) 1) :
    Real.artanh v = (Real.log (1 + v) - Real.log (1 - v)) / 2 := by
  rw [Real.artanh_eq_half_log ⟨hv.1.le, hv.2.le⟩,
    Real.log_div (by linarith [hv.1]) (by linarith [hv.2])]
  ring

end LeanBlast.CourtadeKumar

end

end OAI

-- ---- from OAI.InformationTheory.BooleanNoise.EntropySeries ----
namespace OAI

noncomputable section

open Set Filter Finset
open scoped Topology BigOperators

namespace LeanBlast.CourtadeKumar

theorem hasSum_artanh {v : ℝ} (hv : |v| < 1) :
    HasSum (fun k : ℕ => v ^ (2 * k + 1) / (2 * (k : ℝ) + 1)) (Real.artanh v) := by
  have h := (Real.hasSum_log_sub_log_of_abs_lt_one hv).mul_left (1 / 2)
  convert! h using 1
  · ext k
    ring
  · rw [artanh_eq_log_sub (abs_lt.mp hv)]
    ring

theorem sum_range_artanh_le {v : ℝ} (hv0 : 0 ≤ v) (hv1 : v < 1) (m : ℕ) :
    (∑ k ∈ Finset.range m, v ^ (2 * k + 1) / (2 * (k : ℝ) + 1)) ≤ Real.artanh v := by
  have h := hasSum_artanh (show |v| < 1 by rwa [abs_of_nonneg hv0])
  rw [← h.tsum_eq]
  exact h.summable.sum_le_tsum (Finset.range m) (fun k hk => by positivity)

end LeanBlast.CourtadeKumar

end

end OAI

-- ---- from OAI.InformationTheory.BooleanNoise.LargeCurvature ----
namespace OAI

noncomputable section

open scoped BigOperators

namespace LeanBlast.CourtadeKumar

theorem large_parameter_gt_81 {u : ℝ} (hu0 : 0 ≤ u) (hu2 : (2 / 3 : ℝ) ≤ u ^ 2) :
    (81 / 100 : ℝ) < u := by
  by_contra h
  have hsq := pow_le_pow_left₀ hu0 (le_of_not_gt h) 2
  norm_num at hsq
  linarith

theorem large_artanh_gt_eleven_tenths {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1)
    (hu2 : (2 / 3 : ℝ) ≤ u ^ 2) : (11 / 10 : ℝ) < Real.artanh u := by
  have hu81 := (large_parameter_gt_81 hu0 hu2).le
  have hpoly : (∑ k ∈ Finset.range 5,
      (81 / 100 : ℝ) ^ (2 * k + 1) / (2 * (k : ℝ) + 1)) ≤
      ∑ k ∈ Finset.range 5, u ^ (2 * k + 1) / (2 * (k : ℝ) + 1) := by
    apply Finset.sum_le_sum
    intro k _
    exact div_le_div_of_nonneg_right
      (pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 81 / 100) hu81 _) (by positivity)
  have hnum : (11 / 10 : ℝ) < ∑ k ∈ Finset.range 5,
      (81 / 100 : ℝ) ^ (2 * k + 1) / (2 * (k : ℝ) + 1) := by
    norm_num [Finset.sum_range_succ]
  exact hnum.trans_le (hpoly.trans (sum_range_artanh_le hu0 hu1 5))

theorem entropy_eq_large_parameter_form {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1) :
    entropy u = (1 - u) * Real.artanh u + Real.log (1 + (1 - u) / (1 + u)) := by
  have hp : 0 < 1 + u := by linarith
  have heq : 1 + (1 - u) / (1 + u) = 2 / (1 + u) := by
    field_simp
    ring
  rw [heq, Real.log_div (by norm_num : (2 : ℝ) ≠ 0) hp.ne',
    artanh_eq_log_sub ⟨by linarith, hu1⟩]
  unfold entropy psi ell
  ring

theorem large_parameter_polynomial_bound {y : ℝ} (hy0 : 0 ≤ y)
    (hy1 : y ≤ (5 / 11 : ℝ)) :
    (1 / 2 : ℝ) * (1 - y + (1 + y) / 81) * (1 + 10 * y / 9) ^ 2 ≤ 2 / 3 := by
  have hfirst : (1 - y) * (1 + 10 * y / 9) ^ 2 ≤ (13718 / 10935 : ℝ) := by
    have hc : (13718 / 10935 : ℝ) - (1 - y) * (1 + 10 * y / 9) ^ 2 =
        (y - 11 / 30) ^ 2 * ((100 / 81 : ℝ) * y + 460 / 243) := by ring
    have hp : 0 ≤ (y - 11 / 30) ^ 2 * ((100 / 81 : ℝ) * y + 460 / 243) :=
      mul_nonneg (sq_nonneg _) (by positivity)
    linarith
  have hsecond : (1 + y) * (1 + 10 * y / 9) ^ 2 / 81 ≤
      (355216 / 8732691 : ℝ) := by
    calc
      _ ≤ (1 + (5 / 11 : ℝ)) * (1 + 10 * (5 / 11 : ℝ) / 9) ^ 2 / 81 := by
        gcongr
      _ = _ := by norm_num
  nlinarith

theorem large_curvature_bound {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1)
    (hu2 : (2 / 3 : ℝ) ≤ u ^ 2) :
    entropy u ^ 2 * (((1 + u ^ 2) * Real.artanh u - u) /
      ((1 - u ^ 2) ^ 2 * (Real.artanh u) ^ 3)) ≤ 2 / 3 := by
  let t : ℝ := Real.artanh u
  let e : ℝ := (1 - u) / (1 + u)
  let y : ℝ := 1 / (2 * t)
  let R : ℝ := 1 + (1 + e) * y
  let A : ℝ := 1 - y + (1 + y) * e ^ 2
  let Q : ℝ := ((1 + u ^ 2) * t - u) / ((1 - u ^ 2) ^ 2 * t ^ 3)
  have ht11 : (11 / 10 : ℝ) < t := large_artanh_gt_eleven_tenths hu0 hu1 hu2
  have ht : 0 < t := by linarith
  have hp : 0 < 1 + u := by linarith
  have hm : 0 < 1 - u := by linarith
  have hsq : 0 < 1 - u ^ 2 := by nlinarith [mul_pos hm hp]
  have he0 : 0 ≤ e := div_nonneg hm.le hp.le
  have he1 : e ≤ (1 / 9 : ℝ) := by
    dsimp only [e]
    apply (div_le_iff₀ hp).mpr
    linarith [large_parameter_gt_81 hu0 hu2]
  have hy0 : 0 ≤ y := by dsimp only [y]; positivity
  have hy1 : y ≤ (5 / 11 : ℝ) := by
    dsimp only [y]
    apply (div_le_iff₀ (by positivity : 0 < 2 * t)).mpr
    linarith
  have hR0 : 0 ≤ R := by dsimp only [R]; positivity
  have hA0 : 0 ≤ A := by
    have hy : 0 ≤ 1 - y := by linarith
    dsimp only [A]
    positivity
  have hQ : 0 ≤ Q := by
    apply div_nonneg
    · nlinarith [mul_nonneg (sq_nonneg u) ht.le]
    · positivity
  have hH0 : 0 ≤ entropy u := entropy_nonneg ⟨by linarith, hu1.le⟩
  have hH : entropy u ≤ (1 - u) * t * R := by
    have hlog : Real.log (1 + e) ≤ e := by
      have h := Real.log_le_sub_one_of_pos (by linarith : 0 < 1 + e)
      linarith
    have hid : entropy u = (1 - u) * t + Real.log (1 + e) :=
      entropy_eq_large_parameter_form hu0 hu1
    have hr : (1 - u) * t * R = (1 - u) * t + e := by
      dsimp only [R, e, y]
      field_simp [ht.ne', hp.ne']
      ring
    rw [hr, hid]
    linarith
  have hcoef : ((1 - u) * t) ^ 2 * Q = (1 / 2 : ℝ) * A := by
    dsimp only [Q, A, e, y]
    field_simp [ht.ne', hp.ne', hsq.ne']
    ring
  have hRsq : R ^ 2 ≤ (1 + 10 * y / 9) ^ 2 := by
    apply pow_le_pow_left₀ hR0
    dsimp only [R]
    nlinarith [mul_le_mul_of_nonneg_right he1 hy0]
  have hA : A ≤ 1 - y + (1 + y) / 81 := by
    have he2 := pow_le_pow_left₀ he0 he1 2
    have hmul := mul_le_mul_of_nonneg_left he2 (by linarith : 0 ≤ 1 + y)
    dsimp only [A]
    nlinarith
  have hprod : A * R ^ 2 ≤ (1 - y + (1 + y) / 81) * (1 + 10 * y / 9) ^ 2 :=
    mul_le_mul hA hRsq (sq_nonneg R) (hA0.trans hA)
  change entropy u ^ 2 * Q ≤ 2 / 3
  calc
    entropy u ^ 2 * Q ≤ ((1 - u) * t * R) ^ 2 * Q :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hH0 hH 2) hQ
    _ = (((1 - u) * t) ^ 2 * Q) * R ^ 2 := by ring
    _ = (1 / 2 : ℝ) * (A * R ^ 2) := by rw [hcoef]; ring
    _ ≤ (1 / 2 : ℝ) * ((1 - y + (1 + y) / 81) * (1 + 10 * y / 9) ^ 2) :=
      mul_le_mul_of_nonneg_left hprod (by norm_num)
    _ ≤ 2 / 3 := by simpa only [mul_assoc] using large_parameter_polynomial_bound hy0 hy1

end LeanBlast.CourtadeKumar

end

end OAI

-- ---- platform node ----
open OAI OAI.LeanBlast OAI.LeanBlast.CourtadeKumar
open scoped BigOperators


theorem solution : type_of% @_root_.OAI.LeanBlast.CourtadeKumar.large_curvature_bound := @_root_.OAI.LeanBlast.CourtadeKumar.large_curvature_bound
