-- Prove2me | solution 1 for OAI.LeanBlast.CourtadeKumar.lambda_truncated_upper
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T12:45:46.602662+00:00
-- url     : https://prove2.me/submissions/bba8a43f-f981-4535-9018-3151887878db

-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/BooleanNoise/PerspectiveInequality.lean:L39-L58
-- (upload_full_project.md Phase 4): solution for node OAI.LeanBlast.CourtadeKumar.lambda_truncated_upper. The node keeps its source
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
import Theorems.Thm_OAI_LeanBlast_CourtadeKumar_hasSum_lambda

-- ---- from OAI.InformationTheory.BooleanNoise.PerspectiveInequality ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

noncomputable section

open scoped BigOperators Topology
open Set Filter

namespace LeanBlast.CourtadeKumar

theorem lambda_truncated_upper {z : ℝ} (hz0 : 0 ≤ z) (hz1 : z < 1) (k m : ℕ) :
    (1 - z ^ k) * lambda z ≤
      (∑ j ∈ Finset.range k, z ^ j / ((j : ℝ) + 1)) -
      ∑ j ∈ Finset.range m,
        (z ^ k * (z ^ j / ((j : ℝ) + 1)) -
          z ^ (j + k) / ((j : ℝ) + k + 1)) := by
  have hs := hasSum_lambda hz0 hz1
  have ht := (hasSum_nat_add_iff' k).mpr hs
  have hd := (hs.mul_left (z ^ k)).sub ht
  simp only [Nat.cast_add] at hd
  have hnonneg : ∀ j : ℕ,
      0 ≤ z ^ k * (z ^ j / ((j : ℝ) + 1)) -
        z ^ (j + k) / ((j : ℝ) + k + 1) := by
    intro j
    rw [sub_nonneg, ← mul_div_assoc, ← pow_add, Nat.add_comm k j]
    apply div_le_div_of_nonneg_left (pow_nonneg hz0 _) (by positivity)
    have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    linarith
  have hp := sum_le_hasSum (Finset.range m) (fun j _ => hnonneg j) hd
  linarith

end LeanBlast.CourtadeKumar

end

end OAI

-- ---- platform node ----
open OAI OAI.LeanBlast OAI.LeanBlast.CourtadeKumar
open scoped BigOperators Topology
open Set Filter


theorem solution : type_of% @_root_.OAI.LeanBlast.CourtadeKumar.lambda_truncated_upper := @_root_.OAI.LeanBlast.CourtadeKumar.lambda_truncated_upper
