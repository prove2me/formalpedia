-- Prove2me | solution 1 for OAI.LeanBlast.CourtadeKumar.curvatureNumerator_upper
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T15:30:32.365632+00:00
-- url     : https://prove2.me/submissions/8bd8b8c2-a0d1-49c3-959f-b998ed7f22cf

-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/BooleanNoise/MediumCurvature.lean:L77-L103
-- (upload_full_project.md Phase 4): solution for node OAI.LeanBlast.CourtadeKumar.curvatureNumerator_upper. The node keeps its source
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

-- ---- from OAI.InformationTheory.BooleanNoise.EntropyScalars ----
namespace OAI

noncomputable section

open Set Filter
open scoped Topology

namespace LeanBlast.CourtadeKumar

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

end LeanBlast.CourtadeKumar

end

end OAI

-- ---- from OAI.InformationTheory.BooleanNoise.MediumCurvature ----
namespace OAI

noncomputable section

open Finset Set
open scoped BigOperators

namespace LeanBlast.CourtadeKumar

theorem curvatureNumeratorCoeff_antitone : Antitone curvatureNumeratorCoeff := by
  intro i j hij
  have hij' : (i : ℝ) ≤ j := by exact_mod_cast hij
  unfold curvatureNumeratorCoeff
  exact add_le_add (one_div_le_one_div_of_le (by positivity) (by linarith))
    (one_div_le_one_div_of_le (by positivity) (by linarith))

theorem hasSum_artanh_div {u : ℝ} (hu0 : 0 < u) (hu1 : u < 1) :
    HasSum (fun k : ℕ => (1 / (2 * (k : ℝ) + 1)) * (u ^ 2) ^ k)
      (Real.artanh u / u) := by
  have h := (hasSum_artanh (show |u| < 1 by rwa [abs_of_pos hu0])).div_const u
  convert! h using 1
  ext k
  rw [pow_add, pow_one, ← pow_mul]
  field_simp

theorem hasSum_curvatureNumerator {u : ℝ} (hu0 : 0 < u) (hu1 : u < 1) :
    HasSum (fun k : ℕ => curvatureNumeratorCoeff k * (u ^ 2) ^ k)
      (((1 + u ^ 2) * Real.artanh u - u) / u ^ 3) := by
  have hA := hasSum_artanh_div hu0 hu1
  have htail := (hasSum_nat_add_iff' 1).mpr hA
  have hB : HasSum (fun k : ℕ => (1 / (2 * (k : ℝ) + 3)) * (u ^ 2) ^ k)
      ((Real.artanh u / u - 1) / u ^ 2) := by
    have hdiv := htail.div_const (u ^ 2)
    convert! hdiv using 1
    · ext k
      simp only [Nat.cast_add, Nat.cast_one]
      rw [pow_succ]
      field_simp
      ring
    · simp
  convert hA.add hB using 1
  · ext k
    unfold curvatureNumeratorCoeff
    ring
  · field_simp
    ring

theorem curvatureNumerator_upper {u : ℝ} (hu0 : 0 < u) (hu1 : u < 1) :
    (((1 + u ^ 2) * Real.artanh u - u) / u ^ 3) ≤
      curvatureN (u ^ 2) / (1 - u ^ 2) := by
  have hz0 : 0 ≤ u ^ 2 := sq_nonneg u
  have hz1 : u ^ 2 < 1 := by nlinarith [mul_pos hu0 (sub_pos.mpr hu1)]
  have hz : 1 - u ^ 2 ≠ 0 := by linarith
  have hA := hasSum_curvatureNumerator hu0 hu1
  have htail := (hasSum_nat_add_iff' 5).mpr hA
  have hgeo := (hasSum_geometric_of_lt_one hz0 hz1).mul_left
    (curvatureNumeratorCoeff 5 * (u ^ 2) ^ 5)
  have hbound := hasSum_le
    (fun k : ℕ => calc
      curvatureNumeratorCoeff (k + 5) * (u ^ 2) ^ (k + 5) ≤
          curvatureNumeratorCoeff 5 * (u ^ 2) ^ (k + 5) :=
        mul_le_mul_of_nonneg_right
          (curvatureNumeratorCoeff_antitone (by omega)) (pow_nonneg hz0 _)
      _ = (curvatureNumeratorCoeff 5 * (u ^ 2) ^ 5) * (u ^ 2) ^ k := by
        rw [pow_add]
        ring) htail hgeo
  have hpartial :
      (∑ k ∈ Finset.range 5, curvatureNumeratorCoeff k * (u ^ 2) ^ k) +
          (curvatureNumeratorCoeff 5 * (u ^ 2) ^ 5) * (1 - u ^ 2)⁻¹ =
        curvatureN (u ^ 2) / (1 - u ^ 2) := by
    norm_num [curvatureNumeratorCoeff, Finset.sum_range_succ, curvatureN]
    field_simp
  rw [← hpartial]
  linarith

end LeanBlast.CourtadeKumar

end

end OAI

-- ---- platform node ----
open OAI OAI.LeanBlast OAI.LeanBlast.CourtadeKumar
open Finset Set
open scoped BigOperators


theorem solution : type_of% @_root_.OAI.LeanBlast.CourtadeKumar.curvatureNumerator_upper := @_root_.OAI.LeanBlast.CourtadeKumar.curvatureNumerator_upper
