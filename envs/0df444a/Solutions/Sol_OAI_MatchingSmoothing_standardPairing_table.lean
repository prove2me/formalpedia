-- Prove2me | solution 1 for OAI.MatchingSmoothing.standardPairing_table
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T06:10:59.808994+00:00
-- url     : https://prove2.me/submissions/26f965a6-8ccd-4795-93a3-95a81345576e

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/MatchingPSD/MatchingIncidence.lean:L48-L70
-- (upload_full_project.md Phase 4): solution for node OAI.MatchingSmoothing.standardPairing_table. The node keeps its source
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
import Definitions.Def_OAI_Combinatorics_MatchingPSD_IncidenceKernels
import Definitions.Def_OAI_Combinatorics_MatchingPSD_MatchingIncidence

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

lemma threeEdgeType_symm (a b : Fin 3) : threeEdgeType (a,b) = threeEdgeType (b,a) := by
  fin_cases a <;> fin_cases b <;> rfl

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

-- ---- from OAI.Combinatorics.MatchingPSD.MatchingIncidence ----
namespace OAI

universe u_1 u_2 u_3

namespace MatchingSmoothing

namespace Pairing
variable {V : Type u_1} [Fintype V] [DecidableEq V]

end Pairing

section StandardTable
variable {H : Type u_2} [Fintype H] [DecidableEq H]

omit [DecidableEq H] in
lemma standardPairing_table (f : H × Bool → Fin 3) :
    (standardPairing (H := H)).table f = threeTable f := by
  funext t
  have he : histogram (fun v => threeEdgeType (f v, f ((standardPairing (H := H)).1 v))) t =
      2 * threeTable f t := by
    have hr : (histogram (fun v => threeEdgeType (f v,
        f ((standardPairing (H := H)).1 v))) t : ℝ) = 2 * threeTable f t := by
      simp only [histogram_cast_sum, Fintype.sum_prod_type, Fintype.sum_bool,
        standardPairing, Equiv.prodCongr_apply]
      change (∑ i, ((if threeEdgeType (f (i,true),f (i,false)) = t then (1 : ℝ) else 0) +
        (if threeEdgeType (f (i,false),f (i,true)) = t then 1 else 0))) = _
      simp_rw [threeEdgeType_symm (f (_,true)) (f (_,false))]
      rw [Finset.sum_add_distrib]
      change (∑ i, if threeEdgeType (f (i,false),f (i,true)) = t then (1 : ℝ) else 0) +
        (∑ i, if threeEdgeType (f (i,false),f (i,true)) = t then (1 : ℝ) else 0) = _
      rw [show (threeTable f t : ℝ) =
        ∑ i, if threeEdgeType (f (i,false),f (i,true)) = t then 1 else 0 from
          histogram_cast_sum (threeEdgeType ∘ pairColorEquiv f) t]
      ring
    exact_mod_cast hr
  change _ / 2 = _
  rw [he, Nat.mul_div_right _ (by decide : 0 < 2)]

end StandardTable

section MatchingIncidence
variable {H : Type u_3} [Fintype H] [DecidableEq H]

end MatchingIncidence
end MatchingSmoothing

end OAI

-- ---- platform node ----
open OAI OAI.MatchingSmoothing


theorem solution : type_of% @_root_.OAI.MatchingSmoothing.standardPairing_table := @_root_.OAI.MatchingSmoothing.standardPairing_table
