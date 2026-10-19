-- Prove2me | solution 1 for OAI.LeanBlast.CourtadeKumar.medium_curvature_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T12:14:40.768904+00:00
-- url     : https://prove2.me/submissions/bfc52002-33b7-464c-bde2-6648f13eae08

-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/BooleanNoise/MediumCurvature.lean:L105-L153
-- (upload_full_project.md Phase 4): solution for node OAI.LeanBlast.CourtadeKumar.medium_curvature_bound. The node keeps its source
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
import Theorems.Thm_OAI_LeanBlast_CourtadeKumar_bernsteinSum_pos
import Theorems.Thm_OAI_LeanBlast_CourtadeKumar_hasSum_psi

-- ---- from OAI.InformationTheory.BooleanNoise.EntropyScalars ----
namespace OAI

noncomputable section

open Set Filter
open scoped Topology

namespace LeanBlast.CourtadeKumar

theorem entropy_pos {v : ℝ} (hv : v ∈ Ioo (-1) 1) : 0 < entropy v := by
  rw [entropy_eq_binEntropy]
  exact Real.binEntropy_pos (by linarith [hv.1]) (by linarith [hv.2])

theorem artanh_eq_log_sub {v : ℝ} (hv : v ∈ Ioo (-1) 1) :
    Real.artanh v = (Real.log (1 + v) - Real.log (1 - v)) / 2 := by
  rw [Real.artanh_eq_half_log ⟨hv.1.le, hv.2.le⟩,
    Real.log_div (by linarith [hv.1]) (by linarith [hv.2])]
  ring

end LeanBlast.CourtadeKumar

end

end OAI

-- ---- from OAI.InformationTheory.BooleanNoise.CurvatureCertificates ----
namespace OAI

noncomputable section

open scoped BigOperators

namespace LeanBlast.CourtadeKumar

private theorem curvatureBernstein_pos (i : Fin 19) : 0 < curvatureBernstein i := by
  fin_cases i <;> norm_num [curvatureBernstein]

theorem curvaturePolynomial_bernstein (t : ℝ) :
    curvaturePolynomial ((2 / 3) * t) = bernsteinSum 18 curvatureBernstein t := by
  simp only [bernsteinSum, Fin.sum_univ_succ, Fin.val_zero, Fin.val_succ]
  norm_num [curvatureBernstein, Matrix.cons_val_two, Nat.choose_eq_descFactorial_div_factorial,
    Nat.descFactorial, Nat.factorial]
  unfold curvaturePolynomial curvatureT curvatureP curvatureN
  ring

theorem curvatureCertificate_pos {z : ℝ} (hz0 : 0 ≤ z) (hz2 : z ≤ 2 / 3) :
    0 < curvaturePolynomial z := by
  have ht0 : 0 ≤ (3 / 2 : ℝ) * z := by positivity
  have ht1 : (3 / 2 : ℝ) * z ≤ 1 := by linarith
  have h := bernsteinSum_pos 18 curvatureBernstein curvatureBernstein_pos ht0 ht1
  rw [← curvaturePolynomial_bernstein] at h
  have he : (2 / 3 : ℝ) * ((3 / 2) * z) = z := by ring
  simpa only [he] using h

theorem two_lt_exp_347_div_500 : (2 : ℝ) < Real.exp (347 / 500) := by
  refine lt_of_lt_of_le ?_ (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 347 / 500) 5)
  norm_num [Finset.sum_range_succ, Nat.factorial]

theorem ell_lt_347_div_500 : ell < 347 / 500 :=
  (Real.log_lt_iff_lt_exp (by norm_num : (0 : ℝ) < 2)).mpr two_lt_exp_347_div_500

end LeanBlast.CourtadeKumar

end

end OAI

-- ---- from OAI.InformationTheory.BooleanNoise.EntropySeries ----
namespace OAI

noncomputable section

open Set Filter Finset
open scoped Topology BigOperators

namespace LeanBlast.CourtadeKumar

theorem psiCoeff_pos (k : ℕ) : 0 < psiCoeff k := by unfold psiCoeff; positivity

theorem psiCoeff_nonneg (k : ℕ) : 0 ≤ psiCoeff k := (psiCoeff_pos k).le

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

theorem sum_range_psi_le {v : ℝ} (hv : |v| < 1) (m : ℕ) :
    (∑ k ∈ Finset.range m, psiCoeff k * v ^ (2 * (k + 1))) ≤ psi v := by
  have h := hasSum_psi hv
  rw [← h.tsum_eq]
  exact h.summable.sum_le_tsum (Finset.range m) (fun k hk =>
    mul_nonneg (psiCoeff_nonneg k) (Even.pow_nonneg (even_two_mul (k + 1)) v))

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

theorem curvatureT_lower {u : ℝ} (hu0 : 0 < u) (hu1 : u < 1) :
    u * curvatureT (u ^ 2) ≤ Real.artanh u := by
  have h := sum_range_artanh_le hu0.le hu1 6
  convert h using 1
  norm_num [curvatureT, Finset.sum_range_succ]
  ring

theorem curvatureP_upper {u : ℝ} (hu0 : 0 < u) (hu1 : u < 1) :
    entropy u ≤ curvatureP (u ^ 2) := by
  have h := sum_range_psi_le (show |u| < 1 by rwa [abs_of_pos hu0]) 5
  have hs : (∑ k ∈ Finset.range 5, psiCoeff k * u ^ (2 * (k + 1))) =
      u ^ 2 / 2 + (u ^ 2) ^ 2 / 12 + (u ^ 2) ^ 3 / 30 +
        (u ^ 2) ^ 4 / 56 + (u ^ 2) ^ 5 / 90 := by
    norm_num [psiCoeff, Finset.sum_range_succ]
    ring
  rw [hs] at h
  unfold entropy curvatureP
  linarith [ell_lt_347_div_500]

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

theorem medium_curvature_bound {u : ℝ} (hu0 : 0 < u) (hu1 : u < 1)
    (hz : u ^ 2 ≤ (2 / 3 : ℝ)) :
    entropy u ^ 2 * (((1 + u ^ 2) * Real.artanh u - u) /
      ((1 - u ^ 2) ^ 2 * (Real.artanh u) ^ 3)) ≤ 2 / 3 := by
  have hz0 : 0 ≤ u ^ 2 := sq_nonneg u
  have hz1 : 0 < 1 - u ^ 2 := by linarith
  have ht : 0 < Real.artanh u := Real.artanh_pos ⟨hu0, hu1⟩
  have hH : 0 < entropy u := entropy_pos ⟨by linarith, hu1⟩
  have hHP := curvatureP_upper hu0 hu1
  have hP : 0 < curvatureP (u ^ 2) := hH.trans_le hHP
  have hT : 0 < curvatureT (u ^ 2) := by unfold curvatureT; positivity
  have hTl := curvatureT_lower hu0 hu1
  have hN := curvatureNumerator_upper hu0 hu1
  have hnum : (1 + u ^ 2) * Real.artanh u - u ≤
      (curvatureN (u ^ 2) / (1 - u ^ 2)) * u ^ 3 :=
    (div_le_iff₀ (pow_pos hu0 3)).mp hN
  have hu_atanh : u ≤ Real.artanh u := by
    simpa using sum_range_artanh_le hu0.le hu1 1
  have hnum0 : 0 ≤ (1 + u ^ 2) * Real.artanh u - u := by
    nlinarith [mul_nonneg hz0 ht.le]
  have hsq : entropy u ^ 2 ≤ curvatureP (u ^ 2) ^ 2 :=
    pow_le_pow_left₀ hH.le hHP 2
  have hprod := mul_le_mul hsq hnum hnum0 (sq_nonneg (curvatureP (u ^ 2)))
  have hc := curvatureCertificate_pos hz0 hz
  unfold curvaturePolynomial at hc
  have hc' : 3 * curvatureP (u ^ 2) ^ 2 * curvatureN (u ^ 2) <
      2 * (1 - u ^ 2) ^ 3 * curvatureT (u ^ 2) ^ 3 := by linarith
  have hcert : curvatureP (u ^ 2) ^ 2 *
      ((curvatureN (u ^ 2) / (1 - u ^ 2)) * u ^ 3) <
      (2 / 3 : ℝ) * (1 - u ^ 2) ^ 2 * (u * curvatureT (u ^ 2)) ^ 3 := by
    rw [show curvatureP (u ^ 2) ^ 2 *
        ((curvatureN (u ^ 2) / (1 - u ^ 2)) * u ^ 3) =
        (curvatureP (u ^ 2) ^ 2 * curvatureN (u ^ 2) * u ^ 3) / (1 - u ^ 2) by ring]
    apply (div_lt_iff₀ hz1).mpr
    have hc'' := mul_lt_mul_of_pos_right hc' (pow_pos hu0 3)
    nlinarith
  have hpow : (u * curvatureT (u ^ 2)) ^ 3 ≤ (Real.artanh u) ^ 3 :=
    pow_le_pow_left₀ (mul_nonneg hu0.le hT.le) hTl 3
  have hden := mul_le_mul_of_nonneg_left hpow
    (show 0 ≤ (2 / 3 : ℝ) * (1 - u ^ 2) ^ 2 by positivity)
  rw [← mul_div_assoc]
  apply (div_le_iff₀ (mul_pos (pow_pos hz1 2) (pow_pos ht 3))).mpr
  calc
    entropy u ^ 2 * ((1 + u ^ 2) * Real.artanh u - u) ≤
        curvatureP (u ^ 2) ^ 2 *
          ((curvatureN (u ^ 2) / (1 - u ^ 2)) * u ^ 3) := hprod
    _ ≤ (2 / 3 : ℝ) * (1 - u ^ 2) ^ 2 * (u * curvatureT (u ^ 2)) ^ 3 := hcert.le
    _ ≤ (2 / 3 : ℝ) * ((1 - u ^ 2) ^ 2 * (Real.artanh u) ^ 3) := by
      simpa only [mul_assoc] using hden

end LeanBlast.CourtadeKumar

end

end OAI

-- ---- platform node ----
open OAI OAI.LeanBlast OAI.LeanBlast.CourtadeKumar
open Finset Set
open scoped BigOperators


theorem solution : type_of% @_root_.OAI.LeanBlast.CourtadeKumar.medium_curvature_bound := @_root_.OAI.LeanBlast.CourtadeKumar.medium_curvature_bound
