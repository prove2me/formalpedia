-- Prove2me | solution 1 for OAI.PerfectMatchingPSD.slackAffine_vertex
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T14:47:39.407985+00:00
-- url     : https://prove2.me/submissions/ebd45ea7-fb7b-4605-9ef4-c68ffd56cf0e

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/MatchingPSD/AffineSlacks.lean:L19-L38
-- (upload_full_project.md Phase 4): solution for node OAI.PerfectMatchingPSD.slackAffine_vertex. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_PSDEvaluation
import Definitions.Def_OAI_Combinatorics_MatchingPSD_Model
import Definitions.Def_OAI_Combinatorics_MatchingPSD_EdgeProducts__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_Pairings__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_RepresentationDimension__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_ColoringCounts__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_TransitionMatrices__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_TensorBounds__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_TypeProbabilities__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_TableMoments__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_IncidenceKernels__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_MatchingIncidence__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_SpectralContraction__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_EquivariantCompression__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_PolynomialSpaces__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_FiberAverages__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_ScalarSmoothing__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_EdgeMonomials__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_PartialColorings__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_TableCoordinates__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_TablePolynomials__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_PermutationSmoothing__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_MatchingFibers__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_GlobalGeometry__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_AdmissibleTables__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_CutGeometry__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_CellAverages__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_SequentialTests__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_MatrixAverages__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_PolynomialInterpolation__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_MatrixInterpolation__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_GoodCells__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_CellDecoder__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_AffineSlacks

-- ---- from OAI.Combinatorics.MatchingPSD.AffineSlacks ----
namespace OAI

namespace PerfectMatchingPSD
open MatchingSmoothing Finset Matrix
open scoped BigOperators

lemma slackAffine_vertex {n : ℕ} (i : Row n) (M : PerfectMatching n) :
    slackAffine i (matchingPoint M) = slack i M := by
  classical
  cases i with
  | inl e => rfl
  | inr U =>
    simp only [slackAffine, AffineMap.coe_sub, Pi.sub_apply, AffineMap.const_apply,
      LinearMap.coe_toAffineMap, slack]
    congr 1
    rw [LinearMap.sum_apply]
    calc
      _ = ∑ e : Edge n, if Crosses U.1 e ∧ e ∈ M.1 then (1 : ℝ) else 0 := by
        apply Finset.sum_congr rfl
        intro e _
        by_cases h : Crosses U.1 e <;> simp [h, matchingPoint]
      _ = _ := by
        simp only [Finset.sum_boole, crossingCount]
        apply congrArg (fun s : Finset (Edge n) => (s.card : ℝ))
        ext e
        simp [and_comm]

end PerfectMatchingPSD

end OAI

-- ---- platform node ----
open OAI OAI.PerfectMatchingPSD
open MatchingSmoothing Finset Matrix
open scoped BigOperators


theorem solution : type_of% @_root_.OAI.PerfectMatchingPSD.slackAffine_vertex := @_root_.OAI.PerfectMatchingPSD.slackAffine_vertex
