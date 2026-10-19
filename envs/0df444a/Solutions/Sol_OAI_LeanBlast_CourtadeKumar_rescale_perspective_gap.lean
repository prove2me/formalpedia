-- Prove2me | solution 1 for OAI.LeanBlast.CourtadeKumar.rescale_perspective_gap
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T12:35:35.143887+00:00
-- url     : https://prove2.me/submissions/1d99effd-e70c-491c-9c37-5aacc295a3c3

-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/BooleanNoise/JensenGaps.lean:L206-L226
-- (upload_full_project.md Phase 4): solution for node OAI.LeanBlast.CourtadeKumar.rescale_perspective_gap. The node keeps its source
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

-- ---- from OAI.InformationTheory.BooleanNoise.JensenGaps ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

noncomputable section

open scoped BigOperators

universe u

namespace LeanBlast.CourtadeKumar

section Weighted

variable {ι : Type u} [Fintype ι]

private theorem rescale_perspective_gap (w t b : ι → ℝ) (T k C : ℝ)
    (ht : ∀ i, 0 < t i) (hT : 0 < T)
    (hgap : ((∑ i, (w i * t i / T) * (b i / t i) ^ 2) - (k / T) ^ 2) * C ≤
      2 * ((∑ i, (w i * t i / T) * psi (b i / t i)) - psi (k / T))) :
    ((∑ i, w i * (b i) ^ 2 / t i) - k ^ 2 / T) * C ≤
      2 * ((∑ i, w i * t i * psi (b i / t i)) - T * psi (k / T)) := by
  have hsecond : (∑ i, (w i * t i / T) * (b i / t i) ^ 2) =
      (∑ i, w i * (b i) ^ 2 / t i) / T := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i _
    field_simp [(ht i).ne']
  have hentropy : (∑ i, (w i * t i / T) * psi (b i / t i)) =
      (∑ i, w i * t i * psi (b i / t i)) / T := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hsecond, hentropy] at hgap
  have h := mul_le_mul_of_nonneg_left hgap hT.le
  convert! h using 1 <;> field_simp

end Weighted

end LeanBlast.CourtadeKumar

end

end OAI

-- ---- platform node ----
open OAI OAI.LeanBlast OAI.LeanBlast.CourtadeKumar
open scoped BigOperators


theorem solution.{u} : type_of% @_root_.OAI.LeanBlast.CourtadeKumar.rescale_perspective_gap.{u} := @_root_.OAI.LeanBlast.CourtadeKumar.rescale_perspective_gap.{u}
