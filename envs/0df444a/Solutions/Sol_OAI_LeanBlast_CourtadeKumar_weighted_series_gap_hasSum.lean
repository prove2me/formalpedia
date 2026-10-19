-- Prove2me | solution 1 for OAI.LeanBlast.CourtadeKumar.weighted_series_gap_hasSum
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T12:34:03.240976+00:00
-- url     : https://prove2.me/submissions/228ca76e-c7da-441a-81c3-54bd46894c3b

-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/BooleanNoise/JensenGaps.lean:L104-L122
-- (upload_full_project.md Phase 4): solution for node OAI.LeanBlast.CourtadeKumar.weighted_series_gap_hasSum. The node keeps its source
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

theorem weighted_series_gap_hasSum (c : ℕ → ℝ) (p : ℕ → ℕ) (F : ℝ → ℝ)
    (w x : ι → ℝ) (y : ℝ)
    (hx : ∀ i, HasSum (fun j => c j * (x i) ^ (p j)) (F (x i)))
    (hy : HasSum (fun j => c j * y ^ (p j)) (F y)) :
    HasSum (fun j => 2 * c j * ((∑ i, w i * (x i) ^ (p j)) - y ^ (p j)))
      (2 * ((∑ i, w i * F (x i)) - F y)) := by
  have hsum := hasSum_sum (s := Finset.univ) (fun i _ => (hx i).mul_left (w i))
  have h := (hsum.sub hy).mul_left 2
  have heq : ∀ j, (∑ i, w i * (c j * (x i) ^ (p j))) =
      c j * (∑ i, w i * (x i) ^ (p j)) := by
    intro j
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  simp_rw [heq] at h
  convert! h using 1
  ext j
  ring

end Weighted

end LeanBlast.CourtadeKumar

end

end OAI

-- ---- platform node ----
open OAI OAI.LeanBlast OAI.LeanBlast.CourtadeKumar
open scoped BigOperators


theorem solution.{u} : type_of% @_root_.OAI.LeanBlast.CourtadeKumar.weighted_series_gap_hasSum.{u} := @_root_.OAI.LeanBlast.CourtadeKumar.weighted_series_gap_hasSum.{u}
