-- Prove2me | solution 1 for OAI.LeanBlast.CourtadeKumar.monotone_split_parameter_bounds
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T12:48:15.557195+00:00
-- url     : https://prove2.me/submissions/15df7444-07f1-4795-9d57-66cee08d6642

-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/BooleanNoise/MonotoneDissipation.lean:L118-L138
-- (upload_full_project.md Phase 4): solution for node OAI.LeanBlast.CourtadeKumar.monotone_split_parameter_bounds. The node keeps its source
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

-- ---- from OAI.InformationTheory.BooleanNoise.MonotoneDissipation ----
namespace OAI

noncomputable section

open scoped BigOperators
open Set

namespace LeanBlast.CourtadeKumar

theorem scalar_meanVariance_pos {m : ℝ} (hm : |m| < 1) : 0 < 1 - m ^ 2 := by
  have hsq := (sq_lt_sq₀ (abs_nonneg m) (by norm_num : (0 : ℝ) ≤ 1)).mpr hm
  rw [sq_abs] at hsq
  nlinarith

theorem scalar_meanVariance_le_one (m : ℝ) : 1 - m ^ 2 ≤ 1 := by
  nlinarith [sq_nonneg m]

theorem halfDifference_sq_lt_meanVariance {m k : ℝ}
    (hm : |m| < 1) (hk : 0 ≤ k) (hkm : k < 1 - |m|) :
    k ^ 2 < 1 - m ^ 2 := by
  have hsq := (sq_lt_sq₀ hk (sub_nonneg.mpr hm.le)).mpr hkm
  have ha : |m| ^ 2 ≤ |m| := by
    nlinarith [mul_nonneg (abs_nonneg m) (sub_nonneg.mpr hm.le)]
  nlinarith [sq_abs m]

theorem monotone_split_parameter_bounds {m k W : ℝ}
    (hm : |m| < 1) (hk : 0 ≤ k) (hkm : k < 1 - |m|)
    (hW : 0 < W) (hWA : W ≤ 1 - m ^ 2) (hkW : k ≤ W) :
    0 ≤ k ^ 2 / (1 - m ^ 2) ∧ k ^ 2 / (1 - m ^ 2) < 1 ∧
      0 < W / (1 - m ^ 2) ∧ W / (1 - m ^ 2) ≤ 1 ∧
      k ^ 2 / (1 - m ^ 2) ≤ (W / (1 - m ^ 2)) ^ 2 := by
  have hA := scalar_meanVariance_pos hm
  have hA1 := scalar_meanVariance_le_one m
  refine ⟨div_nonneg (sq_nonneg _) hA.le,
    (div_lt_one hA).mpr (halfDifference_sq_lt_meanVariance hm hk hkm),
    div_pos hW hA, (div_le_one hA).mpr hWA, ?_⟩
  have hk2W2 : k ^ 2 ≤ W ^ 2 := (sq_le_sq₀ hk hW.le).mpr hkW
  have hk2A : k ^ 2 * (1 - m ^ 2) ≤ W ^ 2 := by
    calc
      k ^ 2 * (1 - m ^ 2) ≤ k ^ 2 * 1 :=
        mul_le_mul_of_nonneg_left hA1 (sq_nonneg _)
      _ = k ^ 2 := mul_one _
      _ ≤ W ^ 2 := hk2W2
  rw [div_pow]
  apply (div_le_div_iff₀ hA (sq_pos_of_pos hA)).mpr
  nlinarith [mul_le_mul_of_nonneg_right hk2A hA.le]

end LeanBlast.CourtadeKumar

end

end OAI

-- ---- platform node ----
open OAI OAI.LeanBlast OAI.LeanBlast.CourtadeKumar
open scoped BigOperators
open Set


theorem solution : type_of% @_root_.OAI.LeanBlast.CourtadeKumar.monotone_split_parameter_bounds := @_root_.OAI.LeanBlast.CourtadeKumar.monotone_split_parameter_bounds
