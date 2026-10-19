-- Prove2me | solution 1 for OAI.MatchingSmoothing.tableGamma_rowsum
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T06:01:57.067742+00:00
-- url     : https://prove2.me/submissions/c61ed009-770b-45db-85bc-f3564ed9f834

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/MatchingPSD/TableMoments.lean:L154-L170
-- (upload_full_project.md Phase 4): solution for node OAI.MatchingSmoothing.tableGamma_rowsum. The node keeps its source
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

lemma endpoint_type_identity (a b i : Fin 3) :
    (∑ j : Fin 3, (if threeEdgeType (a,b) = threeEdgeType (i,j) then (1 : ℝ) else 0) /
      typeMultiplicity (threeEdgeType (i,j))) =
      ((if a = i then (1 : ℝ) else 0) + (if b = i then 1 else 0)) / 2 := by
  have h0 : typeMultiplicity 0 = 1 := by decide
  have h1 : typeMultiplicity 1 = 2 := by decide
  have h2 : typeMultiplicity 2 = 2 := by decide
  have h3 : typeMultiplicity 3 = 1 := by decide
  have h4 : typeMultiplicity 4 = 2 := by decide
  have h5 : typeMultiplicity 5 = 1 := by decide
  fin_cases a <;> fin_cases b <;> fin_cases i <;>
    norm_num [threeEdgeType, Fin.sum_univ_succ, Fin.ext_iff, h0, h1, h2, h3, h4, h5]

section ThreeTables
variable {H : Type u_3} [Fintype H] [DecidableEq H]

omit [DecidableEq H] in
lemma histogram_cast_sum {V : Type u_4} {T : Type u_5} [Fintype V] [DecidableEq T] (f : V → T) (t : T) :
    (histogram f t : ℝ) = ∑ i, if f i = t then 1 else 0 := by
  classical
  simp only [histogram, Fintype.card_subtype, Finset.card_filter, Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro i _
  split_ifs <;> norm_num

omit [DecidableEq H] in
lemma tableGamma_rowsum (f : H × Bool → Fin 3) (i : Fin 3) :
    ∑ j, tableGamma f i j = tablePi f i := by
  have he (j : Fin 3) : tableGamma f i j =
      (∑ v : H, (if threeEdgeType (f (v,false),f (v,true)) = threeEdgeType (i,j)
        then (1 : ℝ) else 0) / typeMultiplicity (threeEdgeType (i,j))) / Fintype.card H := by
    simp only [tableGamma, threeTable, histogram_cast_sum, Function.comp_apply,
      pairColorEquiv, Equiv.coe_fn_mk, ← Finset.sum_div]
    ring
  simp_rw [he]
  rw [← Finset.sum_div, Finset.sum_comm]
  simp_rw [endpoint_type_identity]
  rw [← Finset.sum_div, div_div]
  congr 1
  simp only [histogram_cast_sum, Fintype.sum_prod_type, Fintype.sum_bool,
    Finset.sum_add_distrib]
  ring

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


theorem solution : type_of% @_root_.OAI.MatchingSmoothing.tableGamma_rowsum := @_root_.OAI.MatchingSmoothing.tableGamma_rowsum
