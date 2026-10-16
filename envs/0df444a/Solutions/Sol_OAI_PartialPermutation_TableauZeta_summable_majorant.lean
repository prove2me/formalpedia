-- Prove2me | solution 1 for OAI.PartialPermutation.TableauZeta.summable_majorant
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T21:27:45.12819+00:00
-- url     : https://prove2.me/submissions/01a67641-4701-4d82-a36d-ca65b3c40d50

-- Generated from openai/math@1581d4c lean/OAI/RepresentationTheory/PartialPermutation/TableauWeights.lean:L35-L50
-- (upload_full_project.md Phase 4): solution for node OAI.PartialPermutation.TableauZeta.summable_majorant. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_PartialPermutation
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_SchurAverage
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_ModuleTransport
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_Components
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_CentralKernels
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_CompleteKernels
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_RegularRepresentation
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_Plancherel
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_TrivialRepresentation
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_ConvolutionKernels
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_ComponentGeometry
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_SmallKernels
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_ProjectionCovers
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_Restriction
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_IsotypicMatrices
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_IsotypicKernels
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_Equivalences
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_SymmetricTransfer
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_StandardTableaux
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_RankFillings
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_DiagonalBounds
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_FillingExtensions
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_Interleavings
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_RowBounds
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_Truncation
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_TailBounds
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_DiagramCounts
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_DeficitCounts
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_TableauWeights
import Theorems.Thm_OAI_PartialPermutation_DiagramCounting_partitionCount_subexponential

-- ---- from OAI.RepresentationTheory.PartialPermutation.TableauWeights ----
namespace OAI

section
namespace PartialPermutation
namespace TableauZeta
noncomputable section
open Finset Filter
open Tableau DiagramCounting

lemma summable_majorant (u : ℝ) (hu : 0 < u) : Summable (majorant u) := by
  let a := u*Real.log 2/8
  have ha : 0 < a := by dsimp [a]; exact div_pos (mul_pos hu (Real.log_pos (by norm_num))) (by norm_num)
  have hs : Summable (fun k : ℕ => (2*Real.exp (u*Real.log 2))*Real.exp ((k:ℝ)*(-a/2))) :=
    (Real.summable_exp_nat_mul_iff.mpr (by linarith)).mul_left _
  apply hs.of_norm_bounded_eventually_nat
  filter_upwards [partitionCount_subexponential (a/2) (by positivity)] with k hk
  rw [Real.norm_eq_abs,abs_of_nonneg (show 0 ≤ majorant u k by unfold majorant; positivity)]
  calc
    majorant u k ≤ 2*Real.exp ((a/2)*k)*Real.exp (u*Real.log 2-a*k) := by
      unfold majorant
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hk (by norm_num)) (Real.exp_nonneg _)
    _ = (2*Real.exp (u*Real.log 2))*Real.exp ((k:ℝ)*(-a/2)) := by
      rw [mul_assoc,← Real.exp_add,mul_assoc,← Real.exp_add]
      congr 2
      ring

end
end TableauZeta
end PartialPermutation
end

end OAI

-- ---- platform node ----
open OAI OAI.PartialPermutation OAI.PartialPermutation.TableauZeta
open Finset Filter
open Tableau DiagramCounting


theorem solution : type_of% @_root_.OAI.PartialPermutation.TableauZeta.summable_majorant := @_root_.OAI.PartialPermutation.TableauZeta.summable_majorant
