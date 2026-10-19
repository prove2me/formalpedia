-- Prove2me | solution 1 for OAI.LeanBlast.CourtadeKumar.hasSum_lambda
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T12:31:25.791482+00:00
-- url     : https://prove2.me/submissions/5532b1be-9df6-4891-9023-3d76b8713e6e

-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/BooleanNoise/LambdaScalars.lean:L27-L41
-- (upload_full_project.md Phase 4): solution for node OAI.LeanBlast.CourtadeKumar.hasSum_lambda. The node keeps its source
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

-- ---- from OAI.InformationTheory.BooleanNoise.LambdaScalars ----
namespace OAI

noncomputable section

open scoped BigOperators Topology
open Set Filter

namespace LeanBlast.CourtadeKumar

theorem lambda_of_ne_zero {z : ℝ} (hz : z ≠ 0) :
    lambda z = -Real.log (1 - z) / z := by simp [lambda, hz]

theorem hasSum_lambda {z : ℝ} (hz0 : 0 ≤ z) (hz1 : z < 1) :
    HasSum (fun j : ℕ => z ^ j / ((j : ℝ) + 1)) (lambda z) := by
  by_cases hz : z = 0
  · subst z
    rw [lambda_zero]
    convert (hasSum_ite_eq (0 : ℕ) (1 : ℝ)) using 1
    ext j
    by_cases hj : j = 0 <;> simp [hj]
  · have hlog := (Real.hasSum_pow_div_log_of_abs_lt_one
      (show |z| < 1 by rwa [abs_of_nonneg hz0])).div_const z
    rw [lambda_of_ne_zero hz]
    convert! hlog using 1
    ext j
    rw [pow_succ]
    field_simp

end LeanBlast.CourtadeKumar

end

end OAI

-- ---- platform node ----
open OAI OAI.LeanBlast OAI.LeanBlast.CourtadeKumar
open scoped BigOperators Topology
open Set Filter


theorem solution : type_of% @_root_.OAI.LeanBlast.CourtadeKumar.hasSum_lambda := @_root_.OAI.LeanBlast.CourtadeKumar.hasSum_lambda
