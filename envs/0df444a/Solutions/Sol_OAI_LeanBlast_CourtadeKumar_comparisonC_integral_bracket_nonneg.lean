-- Prove2me | solution 1 for OAI.LeanBlast.CourtadeKumar.comparisonC_integral_bracket_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T11:57:53.936097+00:00
-- url     : https://prove2.me/submissions/043cb604-4d28-4c02-a8a0-62a6fe2b538a

-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/BooleanNoise/ComparisonEstimates.lean:L96-L113
-- (upload_full_project.md Phase 4): solution for node OAI.LeanBlast.CourtadeKumar.comparisonC_integral_bracket_nonneg. The node keeps its source
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

-- ---- from OAI.InformationTheory.BooleanNoise.ComparisonEstimates ----
namespace OAI

noncomputable section

open Set

namespace LeanBlast.CourtadeKumar

theorem comparisonC_eq_log_div {u : ℝ} (hu : 0 < u) :
    comparisonC u = 100 / 81 + Real.log ((9 / 10) / u) := by
  rw [Real.log_div (by norm_num : (9 / 10 : ℝ) ≠ 0) hu.ne']
  unfold comparisonC
  ring

theorem comparisonC_integral_bracket_nonneg {u : ℝ}
    (hu : 0 < u) (hu9 : u ≤ (9 / 10 : ℝ)) :
    0 ≤ 1 - u ^ 2 * comparisonC u := by
  have hlog := Real.log_le_sub_one_of_pos
    (div_pos (by norm_num : (0 : ℝ) < 9 / 10) hu)
  have hC : comparisonC u ≤ 100 / 81 + (9 / 10) / u - 1 := by
    rw [comparisonC_eq_log_div hu]
    linarith
  have hmul := mul_le_mul_of_nonneg_left hC (sq_nonneg u)
  have heq : u ^ 2 * (100 / 81 + (9 / 10) / u - 1) =
      (19 / 81 : ℝ) * u ^ 2 + (9 / 10 : ℝ) * u := by
    field_simp
    ring
  rw [heq] at hmul
  have hu2 : u ^ 2 ≤ (9 / 10 : ℝ) ^ 2 := by
    nlinarith [mul_nonneg (show 0 ≤ (9 / 10 : ℝ) - u by linarith)
      (show 0 ≤ (9 / 10 : ℝ) + u by linarith)]
  nlinarith

end LeanBlast.CourtadeKumar

end

end OAI

-- ---- platform node ----
open OAI OAI.LeanBlast OAI.LeanBlast.CourtadeKumar
open Set


theorem solution : type_of% @_root_.OAI.LeanBlast.CourtadeKumar.comparisonC_integral_bracket_nonneg := @_root_.OAI.LeanBlast.CourtadeKumar.comparisonC_integral_bracket_nonneg
