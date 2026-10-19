-- Prove2me | solution 1 for OAI.MatchingSmoothing.threeTable_histogram_eq
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T06:03:29.735524+00:00
-- url     : https://prove2.me/submissions/5e88ed71-24a8-4c81-90b4-697e3bb88d7f

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/MatchingPSD/TableMoments.lean:L229-L242
-- (upload_full_project.md Phase 4): solution for node OAI.MatchingSmoothing.threeTable_histogram_eq. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_MatchingPSD
import Definitions.Def_OAI_Combinatorics_MatchingPSD_EdgeProducts
import Definitions.Def_OAI_Combinatorics_MatchingPSD_Pairings
import Definitions.Def_OAI_Combinatorics_MatchingPSD_RepresentationDimension
import Definitions.Def_OAI_Combinatorics_MatchingPSD_ColoringCounts
import Definitions.Def_OAI_Combinatorics_MatchingPSD_TransitionMatrices
import Definitions.Def_OAI_Combinatorics_MatchingPSD_TensorBounds
import Definitions.Def_OAI_Combinatorics_MatchingPSD_TypeProbabilities
import Definitions.Def_OAI_Combinatorics_MatchingPSD_TableMoments
import Theorems.Thm_OAI_MatchingSmoothing_tableGamma_rowsum

-- ---- from OAI.Combinatorics.MatchingPSD.TableMoments ----
namespace OAI

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10

namespace MatchingSmoothing
open Matrix
section TableKernel
variable {H : Type u_1} {C : Type u_2} [Fintype H] [Fintype C] [DecidableEq H] [DecidableEq C]

end TableKernel
end MatchingSmoothing

namespace MatchingSmoothing
open Matrix

section ThreeTables
variable {H : Type u_3} [Fintype H] [DecidableEq H]

omit [DecidableEq H] in
lemma threeTable_histogram_eq {f g : H × Bool → Fin 3} (hH : 0 < Fintype.card H)
    (h : threeTable f = threeTable g) : histogram f = histogram g := by
  have hγ : tableGamma f = tableGamma g := by
    unfold tableGamma
    rw [h]
  funext i
  have he := (tableGamma_rowsum f i).symm.trans
    ((congrArg (fun A : Matrix (Fin 3) (Fin 3) ℝ => ∑ j, A i j) hγ).trans
      (tableGamma_rowsum g i))
  change (histogram f i : ℝ) / (2 * Fintype.card H) =
    (histogram g i : ℝ) / (2 * Fintype.card H) at he
  have hn : (2 * Fintype.card H : ℝ) ≠ 0 := by positivity
  exact_mod_cast (div_left_inj' hn).mp he

end ThreeTables

section Probability
variable {V : Type u_6} {C : Type u_7} [Fintype V] [Fintype C] [DecidableEq V] [DecidableEq C]

end Probability

section TableNormalization
variable {H : Type u_8} {C : Type u_9} [Fintype H] [Fintype C] [DecidableEq H] [DecidableEq C]

end TableNormalization

section ThreeTableMoment
variable {H : Type u_10} [Fintype H] [DecidableEq H]

end ThreeTableMoment
end MatchingSmoothing

end OAI

-- ---- platform node ----
open OAI OAI.MatchingSmoothing
open Matrix


theorem solution : type_of% @_root_.OAI.MatchingSmoothing.threeTable_histogram_eq := @_root_.OAI.MatchingSmoothing.threeTable_histogram_eq
