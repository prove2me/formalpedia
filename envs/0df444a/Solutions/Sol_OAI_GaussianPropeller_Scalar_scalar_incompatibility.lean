-- Prove2me | solution 1 for OAI.GaussianPropeller.Scalar.scalar_incompatibility
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T13:51:09.230003+00:00
-- url     : https://prove2.me/submissions/afcade28-f984-4b2a-b1ae-890083fa9108

-- Generated from openai/math@1581d4c lean/OAI/Probability/GaussianPropeller/Scalar.lean:L605-L632
-- (upload_full_project.md Phase 4): solution for node OAI.GaussianPropeller.Scalar.scalar_incompatibility. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_GaussianPropeller
import Definitions.Def_OAI_Probability_GaussianPropeller_Moments
import Definitions.Def_OAI_Probability_GaussianPropeller_Dual
import Definitions.Def_OAI_Probability_GaussianPropeller_Deletion
import Definitions.Def_OAI_Probability_GaussianPropeller_Translation
import Definitions.Def_OAI_Probability_GaussianPropeller_HeatConvolution
import Definitions.Def_OAI_Probability_GaussianPropeller_Quantile
import Definitions.Def_OAI_Probability_GaussianPropeller_QuantileCalculus
import Definitions.Def_OAI_Probability_GaussianPropeller_HeatMaximum
import Definitions.Def_OAI_Probability_GaussianPropeller_SmoothedConcavity
import Definitions.Def_OAI_Probability_GaussianPropeller_SoftMinimum
import Definitions.Def_OAI_Probability_GaussianPropeller_ConeConcavity
import Definitions.Def_OAI_Probability_GaussianPropeller_OneCell
import Definitions.Def_OAI_Probability_GaussianPropeller_Mills
import Definitions.Def_OAI_Probability_GaussianPropeller_Taylor
import Definitions.Def_OAI_Probability_GaussianPropeller_ProbabilityBounds
import Definitions.Def_OAI_Probability_GaussianPropeller_Attainment
import Definitions.Def_OAI_Probability_GaussianPropeller_PairIntegral
import Definitions.Def_OAI_Probability_GaussianPropeller_ResidualBounds
import Definitions.Def_OAI_Probability_GaussianPropeller_Polar
import Definitions.Def_OAI_Probability_GaussianPropeller_CapIntegral
import Definitions.Def_OAI_Probability_GaussianPropeller_Coordinates
import Definitions.Def_OAI_Probability_GaussianPropeller_CapBounds
import Definitions.Def_OAI_Probability_GaussianPropeller_CapNumeric
import Definitions.Def_OAI_Probability_GaussianPropeller_Geometry
import Definitions.Def_OAI_Probability_GaussianPropeller_QuarticCertificates
import Definitions.Def_OAI_Probability_GaussianPropeller_CapCertificates
import Definitions.Def_OAI_Probability_GaussianPropeller_Scalar
import Theorems.Thm_OAI_GaussianPropeller_Scalar_RadiusData_common_charge
import Theorems.Thm_OAI_GaussianPropeller_Scalar_RadiusData_minimum_le_root
import Theorems.Thm_OAI_GaussianPropeller_Scalar_RadiusData_third_large

-- ---- from OAI.Probability.GaussianPropeller.Scalar ----
namespace OAI

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open scoped RealInnerProductSpace
open scoped RealInnerProductSpace
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal RealInnerProductSpace
open Filter
open scoped Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
open scoped RealInnerProductSpace
open Set Filter
open scoped Topology RealInnerProductSpace
open scoped NNReal
open Set Filter
open scoped Topology RealInnerProductSpace NNReal
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology RealInnerProductSpace
open MeasureTheory Set Filter
open scoped Topology BigOperators
open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace Topology ENNReal
open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace Topology ENNReal
open Metric
open MeasureTheory ProbabilityTheory Set
open scoped RealInnerProductSpace ENNReal

namespace GaussianPropeller
namespace Scalar

theorem third_radius_gt {L u : ℝ} (hu : 0 < u) (hL : L ≤ 8 / 9)
    (hcharge : (1 - L) * (0.415 / u - 0.734) ≤ 0.116) : 0.23 < u := by
  by_contra! h
  have hd : (0.415 : ℝ) / 0.23 ≤ 0.415 / u :=
    div_le_div_of_nonneg_left (by norm_num) hu h
  have hm := mul_le_mul_of_nonneg_left (sub_le_sub_right hd 0.734)
    (show 0 ≤ 1 - L by linarith)
  norm_num at hm
  nlinarith

theorem small_minimum_interval {L u t a b M : ℝ}
    (ht : 0 ≤ t) (htq : t ≤ 0.066) (hL : L ≤ 8 / 9)
    (hua : a ≤ u) (hub : u ≤ b) (ha : 0.066 < a)
    (hden : 0 < 0.415 / b - 0.734) (hM : 0 ≤ M)
    (hrow : (0.116 : ℝ) ≤
      (1 - (b ^ 2 + 2 * (0.066 : ℝ) ^ 2 + M)) * (0.415 / b - 0.734))
    (hmargin : 8 * (0.066 : ℝ) ^ 2 < (a ^ 2 - (0.066 : ℝ) ^ 2) * M)
    (hcharge : (1 - L) * (0.415 / u - 0.734) ≤ 0.116)
    (hdet : (u ^ 2 - t ^ 2) * (L - u ^ 2 - 2 * t ^ 2) ≤ 8 * t ^ 2) : False := by
  have hup : 0 < u := by linarith
  have hb : 0 < b := lt_of_lt_of_le hup hub
  have hd := div_le_div_of_nonneg_left (show (0 : ℝ) ≤ 0.415 by norm_num) hup hub
  have hm := mul_le_mul_of_nonneg_left (sub_le_sub_right hd 0.734)
    (show 0 ≤ 1 - L by linarith)
  have hLc : b ^ 2 + 2 * (0.066 : ℝ) ^ 2 + M ≤ L := by
    have hh := le_of_mul_le_mul_right ((hm.trans hcharge).trans hrow) hden
    linarith
  have hub2 : u ^ 2 ≤ b ^ 2 := by nlinarith
  have hua2 : a ^ 2 ≤ u ^ 2 := by nlinarith
  have ht2 : t ^ 2 ≤ (0.066 : ℝ) ^ 2 := by nlinarith
  have hfirst : a ^ 2 - (0.066 : ℝ) ^ 2 ≤ u ^ 2 - t ^ 2 := by linarith
  have hfirst0 : 0 ≤ u ^ 2 - t ^ 2 := by nlinarith
  have hsecond : M ≤ L - u ^ 2 - 2 * t ^ 2 := by linarith
  have hp := mul_le_mul hfirst hsecond hM hfirst0
  nlinarith

theorem minimum_gt {L u t : ℝ} (ht : 0 ≤ t) (hu : 0.23 < u)
    (hL : L ≤ 8 / 9) (hL2 : 2 * u ^ 2 ≤ L)
    (hcharge : (1 - L) * (0.415 / u - 0.734) ≤ 0.116)
    (hdet : (u ^ 2 - t ^ 2) * (L - u ^ 2 - 2 * t ^ 2) ≤ 8 * t ^ 2) :
    0.066 < t := by
  by_contra! htq
  by_cases hbig : 0.44 ≤ u
  · have ht2 : t ^ 2 ≤ (0.066 : ℝ) ^ 2 := by nlinarith
    have hu2 : (0.44 : ℝ) ^ 2 ≤ u ^ 2 := by nlinarith
    have hfirst : (0.44 : ℝ) ^ 2 - (0.066 : ℝ) ^ 2 ≤ u ^ 2 - t ^ 2 := by linarith
    have hsecond : (0.44 : ℝ) ^ 2 - 2 * (0.066 : ℝ) ^ 2 ≤
        L - u ^ 2 - 2 * t ^ 2 := by linarith
    have hp := mul_le_mul hfirst hsecond (by norm_num)
      (show 0 ≤ u ^ 2 - t ^ 2 by nlinarith)
    norm_num at hp
    nlinarith
  · have hb : u ≤ 0.44 := le_of_lt (lt_of_not_ge hbig)
    by_cases h30 : u ≤ 0.30
    · exact small_minimum_interval (a := 0.23) (b := 0.30) (M := 0.72264)
        ht htq hL hu.le h30 (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) hcharge hdet
    by_cases h35 : u ≤ 0.35
    · exact small_minimum_interval (a := 0.30) (b := 0.35) (M := 0.61198)
        ht htq hL (by linarith) h35 (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) hcharge hdet
    by_cases h41 : u ≤ 0.41
    · exact small_minimum_interval (a := 0.35) (b := 0.41) (M := 0.40621)
        ht htq hL (by linarith) h41 (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) hcharge hdet
    · exact small_minimum_interval (a := 0.41) (b := 0.44) (M := 0.24314)
        ht htq hL (by linarith) hb (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) hcharge hdet

theorem first_constraint_rational {L c t : ℝ}
    (h : (c - t ^ 2) * (L - c - 2 * t ^ 2) ≤ 8 * (3 / Real.pi) ^ 2 * t ^ 2) :
    (c - t ^ 2) * (L - c - 2 * t ^ 2) ≤ 8 * t ^ 2 := by
  have hratio : (3 : ℝ) / Real.pi ≤ 1 :=
    (div_le_one Real.pi_pos).mpr Real.pi_gt_three.le
  have hratio0 : (0 : ℝ) ≤ 3 / Real.pi := by positivity
  have hsq : ((3 : ℝ) / Real.pi) ^ 2 ≤ 1 := by nlinarith
  have hh := mul_le_mul_of_nonneg_right hsq (sq_nonneg t)
  nlinarith

theorem final_contradiction {c t : ℝ} (ht : 0 < t) (ht12 : t < 0.12)
    (hc : 2.6 * t < c)
    (hdet : (3 / 2 : ℝ) * (c - t ^ 2) ^ 2 ≤ 10 * (3 / Real.pi) ^ 2 * t ^ 2) :
    False := by
  have hp : 0 < Real.pi := Real.pi_pos
  have hratio : (3 : ℝ) / Real.pi < 150 / 157 := by
    rw [div_lt_iff₀ hp]
    nlinarith [Real.pi_gt_d2]
  have hratio0 : (0 : ℝ) ≤ 3 / Real.pi := by positivity
  have hratio2 : ((3 : ℝ) / Real.pi) ^ 2 < (150 / 157 : ℝ) ^ 2 := by nlinarith
  have ht2 : 0 < t ^ 2 := sq_pos_of_pos ht
  have htop := mul_lt_mul_of_pos_right hratio2 ht2
  have hc' : (2.48 : ℝ) * t < c - t ^ 2 := by nlinarith
  have hcsq : ((2.48 : ℝ) * t) ^ 2 < (c - t ^ 2) ^ 2 := by nlinarith
  nlinarith

theorem smallRoot_five :
    0.066 < smallRoot 0.929 2 ∧ smallRoot 0.929 2 < 0.109 ∧
    2 * charge 0.929 (smallRoot 0.929 2) = 1 - 0.929 := by
  have hsq := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 61607 / 1000000)
  have hnn := Real.sqrt_nonneg (61607 / 1000000 : ℝ)
  norm_num only [smallRoot, charge] at *
  constructor
  · nlinarith
  constructor
  · nlinarith
  · nlinarith

theorem smallRoot_six :
    0.066 < smallRoot 0.884 3 ∧ smallRoot 0.884 3 < 0.12 ∧
    3 * charge 0.884 (smallRoot 0.884 3) = 1 - 0.884 := by
  have hsq := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 176099 / 3000000)
  have hnn := Real.sqrt_nonneg (176099 / 3000000 : ℝ)
  norm_num only [smallRoot, charge] at *
  constructor
  · nlinarith
  constructor
  · nlinarith
  · nlinarith

theorem regime_five : Regime 0.929 2 := by
  obtain ⟨hl, hu, he⟩ := smallRoot_five
  have hsqrt := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 429)
  have hsqrt0 := Real.sqrt_nonneg (429 : ℝ)
  constructor
  · norm_num
  · norm_num
  · norm_num
  · exact hl
  · simpa using hu.trans (by norm_num : (0.109 : ℝ) < 0.12)
  · exact he
  · norm_num [threshold]; nlinarith
  · norm_num; nlinarith
  · norm_num [charge]
  · norm_num [charge]
  · norm_num [charge]
  · norm_num [clipCoeff, threshold, charge]
  · norm_num [charge]
  · norm_num [finalBudget, charge]
    nlinarith

theorem regime_six : Regime 0.884 3 := by
  obtain ⟨hl, hu, he⟩ := smallRoot_six
  have hsqrt := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 429)
  have hsqrt0 := Real.sqrt_nonneg (429 : ℝ)
  constructor
  · norm_num
  · norm_num
  · norm_num
  · exact hl
  · exact hu
  · exact he
  · norm_num [threshold]; nlinarith
  · norm_num; nlinarith
  · norm_num [charge]
  · norm_num [charge]
  · norm_num [charge]
  · norm_num [clipCoeff, threshold, charge]
  · norm_num [charge]
  · norm_num [finalBudget, charge]
    nlinarith

namespace RadiusData

variable {m : ℕ} {A : ℝ} (D : RadiusData m A)

theorem radius_le {i j : ℕ} (hj : j < m) (hij : i ≤ j) : D.r j ≤ D.r i :=
  D.ordered (show i ∈ Set.Iio m by exact lt_of_le_of_lt hij hj) hj hij

theorem first_two_cap (hm : 2 ≤ m) : D.r 0 ^ 2 + D.r 1 ^ 2 ≤ 8 / 9 := by
  have h0 := D.cap 0 (by omega)
  have h1 := D.cap 1 (by omega)
  have hp0 := D.pos 0 (by omega)
  have hp1 := D.pos 1 (by omega)
  nlinarith

theorem third_twice (hm : 3 ≤ m) : 2 * D.r 2 ^ 2 ≤ D.r 0 ^ 2 + D.r 1 ^ 2 := by
  have hp := D.pos 2 (by omega)
  have h0 := D.radius_le (by omega : 2 < m) (by omega : 0 ≤ 2)
  have h1 := D.radius_le (by omega : 2 < m) (by omega : 1 ≤ 2)
  nlinarith

theorem minimum_lower (hm : 5 ≤ m) (hA : 0.884 ≤ A)
    (hdet : (D.r 2 ^ 2 - D.r (m - 1) ^ 2) *
      (D.r 0 ^ 2 + D.r 1 ^ 2 - D.r 2 ^ 2 - 2 * D.r (m - 1) ^ 2) ≤
        8 * (3 / Real.pi) ^ 2 * D.r (m - 1) ^ 2) :
    0.066 < D.r (m - 1) := by
  have hc := D.common_charge (by omega) hA
  have hL := D.first_two_cap (by omega)
  have hu := third_radius_gt (D.pos 2 (by omega)) hL hc
  exact minimum_gt (D.pos (m - 1) (by omega)).le hu hL
    (D.third_twice (by omega)) hc (first_constraint_rational hdet)

theorem incompatible {k : ℕ} (R : Regime A k) (hm : 5 ≤ m) (hkm : 3 + k ≤ m)
    (hdet₁ : (D.r 2 ^ 2 - D.r (m - 1) ^ 2) *
      (D.r 0 ^ 2 + D.r 1 ^ 2 - D.r 2 ^ 2 - 2 * D.r (m - 1) ^ 2) ≤
        8 * (3 / Real.pi) ^ 2 * D.r (m - 1) ^ 2)
    (hdet₂ : (3 / 2 : ℝ) * (D.r 2 ^ 2 - D.r (m - 1) ^ 2) ^ 2 ≤
      10 * (3 / Real.pi) ^ 2 * D.r (m - 1) ^ 2) : False := by
  have ht := D.minimum_lower hm R.A_lower hdet₁
  have htroot := D.minimum_le_root R hm hkm ht
  have ht12 := lt_of_le_of_lt htroot R.root_upper
  exact final_contradiction (by linarith : 0 < D.r (m - 1)) ht12
    (D.third_large R hm hkm ht) hdet₂

end RadiusData

theorem scalar_incompatibility {m : ℕ} (hm : 5 ≤ m) (r P : ℕ → ℝ)
    (hpos : ∀ i < m, 0 < r i) (hordered : AntitoneOn r (Set.Iio m))
    (hcap : ∀ i < m, r i ≤ 2 / 3)
    (hnorm : ∑ i ∈ Finset.range m, r i ^ 2 = 1)
    (hprob : ∑ i ∈ Finset.range m, P i = 1)
    (hquad : ∀ i < m, (if m = 5 then (0.929 : ℝ) else 0.884) * r i ^ 2 ≤ P i)
    (hlin : ∀ i < m, 0.415 * r i + 0.15 * r i ^ 2 ≤ P i)
    (hdet₁ : (r 2 ^ 2 - r (m - 1) ^ 2) *
      (r 0 ^ 2 + r 1 ^ 2 - r 2 ^ 2 - 2 * r (m - 1) ^ 2) ≤
        8 * (3 / Real.pi) ^ 2 * r (m - 1) ^ 2)
    (hdet₂ : (3 / 2 : ℝ) * (r 2 ^ 2 - r (m - 1) ^ 2) ^ 2 ≤
      10 * (3 / Real.pi) ^ 2 * r (m - 1) ^ 2) : False := by
  let A : ℝ := if m = 5 then 0.929 else 0.884
  let D : RadiusData m A := {
    r := r
    δ := fun i => P i - A * r i ^ 2
    pos := hpos
    ordered := hordered
    cap := hcap
    norm := hnorm
    nonneg := fun i hi => sub_nonneg.mpr (hquad i hi)
    lower := by intro i hi; dsimp [charge]; linarith [hlin i hi]
    budget := by rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hnorm, hprob, mul_one] }
  by_cases hm5 : m = 5
  · have hR : Regime A 2 := by simpa [A, hm5] using regime_five
    exact D.incompatible hR hm (by omega) hdet₁ hdet₂
  · have hR : Regime A 3 := by simpa [A, hm5] using regime_six
    exact D.incompatible hR hm (by omega) hdet₁ hdet₂

end Scalar

end GaussianPropeller

end OAI

-- ---- platform node ----
open OAI OAI.GaussianPropeller OAI.GaussianPropeller.Scalar
open MeasureTheory ProbabilityTheory
open scoped ENNReal
open scoped RealInnerProductSpace
open scoped RealInnerProductSpace
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal RealInnerProductSpace
open Filter
open scoped Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
open scoped RealInnerProductSpace
open Set Filter
open scoped Topology RealInnerProductSpace
open scoped NNReal
open Set Filter
open scoped Topology RealInnerProductSpace NNReal
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology RealInnerProductSpace
open MeasureTheory Set Filter
open scoped Topology BigOperators
open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace Topology ENNReal
open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace Topology ENNReal
open Metric
open MeasureTheory ProbabilityTheory Set
open scoped RealInnerProductSpace ENNReal


theorem solution : type_of% @_root_.OAI.GaussianPropeller.Scalar.scalar_incompatibility := @_root_.OAI.GaussianPropeller.Scalar.scalar_incompatibility
