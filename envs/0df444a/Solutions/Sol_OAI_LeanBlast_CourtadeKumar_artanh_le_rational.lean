-- Prove2me | solution 1 for OAI.LeanBlast.CourtadeKumar.artanh_le_rational
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T12:51:35.119026+00:00
-- url     : https://prove2.me/submissions/e62f33b2-f3f7-4b32-814b-76655357d3c0

-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/BooleanNoise/Comparison.lean:L257-L307
-- (upload_full_project.md Phase 4): solution for node OAI.LeanBlast.CourtadeKumar.artanh_le_rational. The node keeps its source
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
import Definitions.Def_OAI_InformationTheory_BooleanNoise_CurvatureBounds
import Definitions.Def_OAI_InformationTheory_BooleanNoise_LRegularity
import Definitions.Def_OAI_InformationTheory_BooleanNoise_SemigroupFlow
import Definitions.Def_OAI_InformationTheory_BooleanNoise_CubeSplits
import Definitions.Def_OAI_InformationTheory_BooleanNoise_PairEntropy
import Definitions.Def_OAI_InformationTheory_BooleanNoise_LambdaScalars
import Definitions.Def_OAI_InformationTheory_BooleanNoise_JensenGaps
import Definitions.Def_OAI_InformationTheory_BooleanNoise_CubeVariance
import Definitions.Def_OAI_InformationTheory_BooleanNoise_NormalizedPair
import Definitions.Def_OAI_InformationTheory_BooleanNoise_PerspectiveLogTrapezoid
import Definitions.Def_OAI_InformationTheory_BooleanNoise_PerspectiveCalculus
import Definitions.Def_OAI_InformationTheory_BooleanNoise_PerspectiveInequality
import Definitions.Def_OAI_InformationTheory_BooleanNoise_Comparison
import Theorems.Thm_OAI_LeanBlast_CourtadeKumar_hasDerivAt_artanh

-- ---- from OAI.InformationTheory.BooleanNoise.CurvatureCertificates ----
namespace OAI

noncomputable section

open scoped BigOperators

namespace LeanBlast.CourtadeKumar

theorem nineteen_lt_exp_three : (19 : ℝ) < Real.exp 3 := by
  refine lt_of_lt_of_le ?_ (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 3) 7)
  norm_num [Finset.sum_range_succ, Nat.factorial]

theorem log_nineteen_lt_three : Real.log 19 < 3 :=
  (Real.log_lt_iff_lt_exp (by norm_num : (0 : ℝ) < 19)).mpr nineteen_lt_exp_three

end LeanBlast.CourtadeKumar

end

end OAI

-- ---- from OAI.InformationTheory.BooleanNoise.Comparison ----
namespace OAI

noncomputable section

open Set Filter MeasureTheory
open scoped Topology BigOperators

namespace LeanBlast.CourtadeKumar

private theorem sq_lt_one_of_mem {u : ℝ} (hu : u ∈ Ioo (-1) 1) : u ^ 2 < 1 := by
  have hp : 0 < (1 - u) * (u + 1) := mul_pos (by linarith [hu.2]) (by linarith [hu.1])
  nlinarith

theorem hasDerivAt_rationalArtanhGap {u : ℝ} (hu : u ∈ Ioo (-1) 1) :
    HasDerivAt rationalArtanhGap
      (u ^ 2 * (2 - 3 * u ^ 2) / ((2 - u ^ 2) ^ 2 * (1 - u ^ 2))) u := by
  have hsq := sq_lt_one_of_mem hu
  have hden : 1 - u ^ 2 / 2 ≠ 0 := by nlinarith
  have hden' : 1 - u ^ 2 ≠ 0 := by nlinarith
  have hden'' : 2 - u ^ 2 ≠ 0 := by nlinarith
  have hd := ((hasDerivAt_id u).div
    ((hasDerivAt_const u 1).sub (((hasDerivAt_id u).pow 2).div_const 2)) hden).sub
      (hasDerivAt_artanh hu)
  convert! hd using 1
  simp only [id_eq, Pi.sub_apply, Pi.pow_apply]
  field_simp [hden, hden', hden'']
  ring

theorem artanh_le_rational {u : ℝ} (hu : 0 ≤ u) (hu9 : u ≤ 9 / 10) :
    Real.artanh u ≤ u / (1 - u ^ 2 / 2) := by
  let c : ℝ := Real.sqrt (2 / 3)
  have hc0 : 0 ≤ c := Real.sqrt_nonneg _
  have hcsq : c ^ 2 = 2 / 3 := Real.sq_sqrt (by norm_num)
  have hc9 : c < 9 / 10 := by nlinarith
  have hdenpos : ∀ x ∈ Icc (0 : ℝ) (9 / 10),
      0 < (2 - x ^ 2) ^ 2 * (1 - x ^ 2) := by
    intro x hx
    have hsq : x ^ 2 < 1 := sq_lt_one_of_mem ⟨by linarith [hx.1], by linarith [hx.2]⟩
    exact mul_pos (sq_pos_of_pos (by linarith)) (by linarith)
  have hleft : MonotoneOn rationalArtanhGap (Icc 0 c) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 c)
    · intro x hx
      exact (hasDerivAt_rationalArtanhGap ⟨by linarith [hx.1], by linarith [hx.2]⟩).continuousAt.continuousWithinAt
    · intro x hx
      have hx' : x ∈ Icc (0 : ℝ) c := interior_subset hx
      exact (hasDerivAt_rationalArtanhGap ⟨by linarith [hx'.1], by linarith [hx'.2]⟩).hasDerivWithinAt
    · intro x hx
      have hx' : x ∈ Icc (0 : ℝ) c := interior_subset hx
      have hsq : x ^ 2 ≤ c ^ 2 := (sq_le_sq₀ hx'.1 hc0).mpr hx'.2
      exact div_nonneg (mul_nonneg (sq_nonneg _) (by nlinarith))
        (hdenpos x ⟨hx'.1, hx'.2.trans hc9.le⟩).le
  have hright : AntitoneOn rationalArtanhGap (Icc c (9 / 10)) := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc c (9 / 10))
    · intro x hx
      exact (hasDerivAt_rationalArtanhGap ⟨by linarith [hx.1], by linarith [hx.2]⟩).continuousAt.continuousWithinAt
    · intro x hx
      have hx' : x ∈ Icc c (9 / 10 : ℝ) := interior_subset hx
      exact (hasDerivAt_rationalArtanhGap ⟨by linarith [hx'.1], by linarith [hx'.2]⟩).hasDerivWithinAt
    · intro x hx
      have hx' : x ∈ Icc c (9 / 10 : ℝ) := interior_subset hx
      have hx0 : 0 ≤ x := hc0.trans hx'.1
      have hsq : c ^ 2 ≤ x ^ 2 := (sq_le_sq₀ hc0 hx0).mpr hx'.1
      exact div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos (sq_nonneg _) (by nlinarith))
        (hdenpos x ⟨hx0, hx'.2⟩).le
  have hend : 0 ≤ rationalArtanhGap (9 / 10) := by
    have ha : Real.artanh (9 / 10) = Real.log 19 / 2 := by
      rw [Real.artanh_eq_half_log (by norm_num)]
      norm_num
      ring
    unfold rationalArtanhGap
    rw [ha]
    norm_num
    linarith [log_nineteen_lt_three]
  have hgap : 0 ≤ rationalArtanhGap u := by
    by_cases huc : u ≤ c
    · have h := hleft ⟨le_rfl, hc0⟩ ⟨hu, huc⟩ hu
      simpa [rationalArtanhGap] using h
    · exact hend.trans (hright ⟨le_of_not_ge huc, hu9⟩ ⟨hc9.le, le_rfl⟩ hu9)
  exact sub_nonneg.mp hgap

end LeanBlast.CourtadeKumar

end

end OAI

-- ---- platform node ----
open OAI OAI.LeanBlast OAI.LeanBlast.CourtadeKumar
open Set Filter MeasureTheory
open scoped Topology BigOperators


theorem solution : type_of% @_root_.OAI.LeanBlast.CourtadeKumar.artanh_le_rational := @_root_.OAI.LeanBlast.CourtadeKumar.artanh_le_rational
