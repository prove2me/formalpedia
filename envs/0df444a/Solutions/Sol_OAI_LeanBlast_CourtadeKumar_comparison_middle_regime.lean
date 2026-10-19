-- Prove2me | solution 1 for OAI.LeanBlast.CourtadeKumar.comparison_middle_regime
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T11:59:54.722426+00:00
-- url     : https://prove2.me/submissions/5ffea6a0-3f4d-43ef-acfc-4a9acfb75f0b

-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/BooleanNoise/ComparisonEstimates.lean:L130-L149
-- (upload_full_project.md Phase 4): solution for node OAI.LeanBlast.CourtadeKumar.comparison_middle_regime. The node keeps its source
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

-- ---- from OAI.InformationTheory.BooleanNoise.CurvatureCertificates ----
namespace OAI

noncomputable section

open scoped BigOperators

namespace LeanBlast.CourtadeKumar

theorem two_lt_exp_347_div_500 : (2 : ℝ) < Real.exp (347 / 500) := by
  refine lt_of_lt_of_le ?_ (Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 347 / 500) 5)
  norm_num [Finset.sum_range_succ, Nat.factorial]

theorem ell_lt_347_div_500 : ell < 347 / 500 :=
  (Real.log_lt_iff_lt_exp (by norm_num : (0 : ℝ) < 2)).mpr two_lt_exp_347_div_500

end LeanBlast.CourtadeKumar

end

end OAI

-- ---- from OAI.InformationTheory.BooleanNoise.ComparisonEstimates ----
namespace OAI

noncomputable section

open Set

namespace LeanBlast.CourtadeKumar

theorem comparison_middle_regime (m u B P S v : ℝ)
    (hB0 : 0 ≤ B) (hB : B ≤ m ^ 2 * (ell - 1 / 2))
    (hP : u ^ 2 / 2 ≤ P)
    (hS : S ≤ (1 - m ^ 2) * P + B * (1 - v))
    (hv : 1 - v ≤ (5 / 2 : ℝ) * u ^ 2) : S ≤ P := by
  have hell : (ell - 1 / 2) * (5 / 2 : ℝ) ≤ 1 / 2 := by
    have h := ell_lt_347_div_500
    linarith
  have hcorrection : B * (1 - v) ≤ m ^ 2 * P := by
    calc
      B * (1 - v) ≤ B * ((5 / 2 : ℝ) * u ^ 2) :=
        mul_le_mul_of_nonneg_left hv hB0
      _ ≤ (m ^ 2 * (ell - 1 / 2)) * ((5 / 2 : ℝ) * u ^ 2) :=
        mul_le_mul_of_nonneg_right hB (by positivity)
      _ ≤ m ^ 2 * (u ^ 2 / 2) := by
        have h := mul_le_mul_of_nonneg_left hell
          (mul_nonneg (sq_nonneg m) (sq_nonneg u))
        nlinarith
      _ ≤ m ^ 2 * P := mul_le_mul_of_nonneg_left hP (sq_nonneg m)
  nlinarith

end LeanBlast.CourtadeKumar

end

end OAI

-- ---- platform node ----
open OAI OAI.LeanBlast OAI.LeanBlast.CourtadeKumar
open Set


theorem solution : type_of% @_root_.OAI.LeanBlast.CourtadeKumar.comparison_middle_regime := @_root_.OAI.LeanBlast.CourtadeKumar.comparison_middle_regime
