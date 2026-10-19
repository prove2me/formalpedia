-- Prove2me | solution 1 for OAI.LeanBlast.CourtadeKumar.noiseOperator_signProbability
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T15:38:45.503733+00:00
-- url     : https://prove2.me/submissions/a25da267-71ec-44d8-af41-15d219a0b5b5

-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/BooleanNoise/FiniteDistribution.lean:L25-L40
-- (upload_full_project.md Phase 4): solution for node OAI.LeanBlast.CourtadeKumar.noiseOperator_signProbability. The node keeps its source
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
import Definitions.Def_OAI_InformationTheory_BooleanNoise_CurvatureBounds__SoftChannel204
import Definitions.Def_OAI_InformationTheory_BooleanNoise_LRegularity__SoftChannel204
import Definitions.Def_OAI_InformationTheory_BooleanNoise_FiniteNoise__SoftChannel204
import Definitions.Def_OAI_InformationTheory_BooleanNoise_Rearrangement__SoftChannel204
import Definitions.Def_OAI_InformationTheory_BooleanNoise_SemigroupFlow__SoftChannel204
import Definitions.Def_OAI_InformationTheory_BooleanNoise_CubeSplits__SoftChannel204
import Definitions.Def_OAI_InformationTheory_BooleanNoise_PairEntropy__SoftChannel204
import Definitions.Def_OAI_InformationTheory_BooleanNoise_LambdaScalars__SoftChannel204
import Definitions.Def_OAI_InformationTheory_BooleanNoise_JensenGaps__SoftChannel204
import Definitions.Def_OAI_InformationTheory_BooleanNoise_CubeVariance__SoftChannel204
import Definitions.Def_OAI_InformationTheory_BooleanNoise_NormalizedPair__SoftChannel204
import Definitions.Def_OAI_InformationTheory_BooleanNoise_PerspectiveLogTrapezoid__SoftChannel204
import Definitions.Def_OAI_InformationTheory_BooleanNoise_PerspectiveCalculus__SoftChannel204
import Definitions.Def_OAI_InformationTheory_BooleanNoise_PerspectiveInequality__SoftChannel204
import Definitions.Def_OAI_InformationTheory_BooleanNoise_Comparison__SoftChannel204
import Definitions.Def_OAI_InformationTheory_BooleanNoise_Statement__SoftChannel204
import Definitions.Def_OAI_InformationTheory_BooleanNoise_FiniteDistribution__SoftChannel204

-- ---- from OAI.InformationTheory.BooleanNoise.FiniteNoise ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

open scoped BigOperators

noncomputable section

universe u

namespace LeanBlast.CourtadeKumar

variable {n : ℕ}

theorem noiseOperator_add (u : ℝ) (g h : Cube n → ℝ) (x : Cube n) :
    noiseOperator u (fun y => g y + h y) x = noiseOperator u g x + noiseOperator u h x := by
  simp [noiseOperator, mul_add, Finset.sum_add_distrib]

theorem noiseOperator_sub (u : ℝ) (g h : Cube n → ℝ) (x : Cube n) :
    noiseOperator u (fun y => g y - h y) x = noiseOperator u g x - noiseOperator u h x := by
  simp [noiseOperator, mul_sub, Finset.sum_sub_distrib]

theorem noiseOperator_smul (u c : ℝ) (g : Cube n → ℝ) (x : Cube n) :
    noiseOperator u (fun y => c * g y) x = c * noiseOperator u g x := by
  simp [noiseOperator, Finset.mul_sum, mul_left_comm]

end LeanBlast.CourtadeKumar

end

end OAI

-- ---- from OAI.InformationTheory.BooleanNoise.FiniteDistribution ----
namespace OAI

noncomputable section

open scoped BigOperators

namespace LeanBlast.CourtadeKumar

variable {n : ℕ}

theorem noiseOperator_signProbability (u : ℝ) (g : Cube n → ℝ) (b : Bool) (x : Cube n) :
    noiseOperator u (fun y => signProbability (g y) b) x =
      signProbability (noiseOperator u g x) b := by
  cases b
  · change noiseOperator u (fun y => (1 - g y) / 2) x = (1 - noiseOperator u g x) / 2
    have hfun : (fun y => (1 - g y) / 2) = (fun y => (1 / 2 : ℝ) * (1 - g y)) := by
      funext y
      ring
    rw [hfun, noiseOperator_smul, noiseOperator_sub, noiseOperator_const]
    ring
  · change noiseOperator u (fun y => (1 + g y) / 2) x = (1 + noiseOperator u g x) / 2
    have hfun : (fun y => (1 + g y) / 2) = (fun y => (1 / 2 : ℝ) * (1 + g y)) := by
      funext y
      ring
    rw [hfun, noiseOperator_smul, noiseOperator_add, noiseOperator_const]
    ring

end LeanBlast.CourtadeKumar

end

end OAI

-- ---- platform node ----
open OAI OAI.LeanBlast OAI.LeanBlast.CourtadeKumar
open scoped BigOperators


theorem solution : type_of% @_root_.OAI.LeanBlast.CourtadeKumar.noiseOperator_signProbability := @_root_.OAI.LeanBlast.CourtadeKumar.noiseOperator_signProbability
