-- Prove2me | solution 1 for OAI.LeanBlast.CourtadeKumar.IsInterior.pairDomain
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T12:22:55.311041+00:00
-- url     : https://prove2.me/submissions/ac2a334b-7907-4599-9d89-7eed2207b8f0

-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/BooleanNoise/CubeSplits.lean:L186-L202
-- (upload_full_project.md Phase 4): solution for node OAI.LeanBlast.CourtadeKumar.IsInterior.pairDomain. The node keeps its source
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

-- ---- from OAI.InformationTheory.BooleanNoise.CubeSplits ----
namespace OAI

open scoped BigOperators

noncomputable section

namespace LeanBlast.CourtadeKumar

variable {n : ℕ}

theorem IsInterior.restrict {g : Cube (n + 1) → ℝ} (hg : IsInterior g) (b : Bool) :
    IsInterior (LeanBlast.CourtadeKumar.restrict g b) := by
  intro x
  exact hg (Fin.cases b x)

theorem IsInterior.pairDomain {g : Cube (n + 1) → ℝ} (hg : IsInterior g) :
    ∀ x, |LeanBlast.CourtadeKumar.pairMean g x| + |pairHalfDifference g x| < 1 := by
  intro x
  have h1 := hg.restrict true x
  have h0 := hg.restrict false x
  have hsum := pairMean_add_halfDifference g x
  have hsub := pairMean_sub_halfDifference g x
  rcases le_total 0 (LeanBlast.CourtadeKumar.pairMean g x) with ha | ha <;>
    rcases le_total 0 (pairHalfDifference g x) with hb | hb
  · rw [abs_of_nonneg ha, abs_of_nonneg hb]
    linarith
  · rw [abs_of_nonneg ha, abs_of_nonpos hb]
    linarith
  · rw [abs_of_nonpos ha, abs_of_nonneg hb]
    linarith
  · rw [abs_of_nonpos ha, abs_of_nonpos hb]
    linarith

end LeanBlast.CourtadeKumar

end

end OAI

-- ---- platform node ----
open OAI OAI.LeanBlast OAI.LeanBlast.CourtadeKumar
open scoped BigOperators


theorem solution : type_of% @_root_.OAI.LeanBlast.CourtadeKumar.IsInterior.pairDomain := @_root_.OAI.LeanBlast.CourtadeKumar.IsInterior.pairDomain
