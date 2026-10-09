-- Prove2me | solution 1 for OAI.SidorenkoCounterexample.refinement_round_0
-- status  : ACCEPTED   (prove)
-- author  : @abcdefg
-- created : 2026-10-08T17:23:38.934604+00:00
-- url     : https://prove2.me/submissions/265327fc-57c8-4bc6-ab68-c9e7fc4b011c

import Mathlib
import Definitions.Def_SidorenkoRefinementColors
namespace OAI.SidorenkoCounterexample
open scoped BigOperators
def histLeft0 : Fin 13 → Fin 35 → ℕ := ![![0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]
lemma histLeft0_0 : ∀ c, neighborHistogram cornerPoint (fun k : ActCorner => refineRight0 k.1) 0 c=histLeft0 0 c := by decide +kernel
lemma histLeft0_1 : ∀ c, neighborHistogram cornerPoint (fun k : ActCorner => refineRight0 k.1) 1 c=histLeft0 1 c := by decide +kernel
lemma histLeft0_2 : ∀ c, neighborHistogram cornerPoint (fun k : ActCorner => refineRight0 k.1) 2 c=histLeft0 2 c := by decide +kernel
lemma histLeft0_3 : ∀ c, neighborHistogram cornerPoint (fun k : ActCorner => refineRight0 k.1) 3 c=histLeft0 3 c := by decide +kernel
lemma histLeft0_4 : ∀ c, neighborHistogram cornerPoint (fun k : ActCorner => refineRight0 k.1) 4 c=histLeft0 4 c := by decide +kernel
lemma histLeft0_5 : ∀ c, neighborHistogram cornerPoint (fun k : ActCorner => refineRight0 k.1) 5 c=histLeft0 5 c := by decide +kernel
lemma histLeft0_6 : ∀ c, neighborHistogram cornerPoint (fun k : ActCorner => refineRight0 k.1) 6 c=histLeft0 6 c := by decide +kernel
lemma histLeft0_7 : ∀ c, neighborHistogram cornerPoint (fun k : ActCorner => refineRight0 k.1) 7 c=histLeft0 7 c := by decide +kernel
lemma histLeft0_8 : ∀ c, neighborHistogram cornerPoint (fun k : ActCorner => refineRight0 k.1) 8 c=histLeft0 8 c := by decide +kernel
lemma histLeft0_9 : ∀ c, neighborHistogram cornerPoint (fun k : ActCorner => refineRight0 k.1) 9 c=histLeft0 9 c := by decide +kernel
lemma histLeft0_10 : ∀ c, neighborHistogram cornerPoint (fun k : ActCorner => refineRight0 k.1) 10 c=histLeft0 10 c := by decide +kernel
lemma histLeft0_11 : ∀ c, neighborHistogram cornerPoint (fun k : ActCorner => refineRight0 k.1) 11 c=histLeft0 11 c := by decide +kernel
lemma histLeft0_12 : ∀ c, neighborHistogram cornerPoint (fun k : ActCorner => refineRight0 k.1) 12 c=histLeft0 12 c := by decide +kernel
lemma histLeft0_correct : ∀ v c, neighborHistogram cornerPoint (fun k : ActCorner => refineRight0 k.1) v c=histLeft0 v c := by
  intro v; fin_cases v
  · exact histLeft0_0
  · exact histLeft0_1
  · exact histLeft0_2
  · exact histLeft0_3
  · exact histLeft0_4
  · exact histLeft0_5
  · exact histLeft0_6
  · exact histLeft0_7
  · exact histLeft0_8
  · exact histLeft0_9
  · exact histLeft0_10
  · exact histLeft0_11
  · exact histLeft0_12
lemma refineLeft0_iff_0 : ∀ w, refineLeft1 0=refineLeft1 w ↔ refineLeft0 0=refineLeft0 w ∧ histLeft0 0=histLeft0 w := by decide +kernel
lemma refineLeft0_iff_1 : ∀ w, refineLeft1 1=refineLeft1 w ↔ refineLeft0 1=refineLeft0 w ∧ histLeft0 1=histLeft0 w := by decide +kernel
lemma refineLeft0_iff_2 : ∀ w, refineLeft1 2=refineLeft1 w ↔ refineLeft0 2=refineLeft0 w ∧ histLeft0 2=histLeft0 w := by decide +kernel
lemma refineLeft0_iff_3 : ∀ w, refineLeft1 3=refineLeft1 w ↔ refineLeft0 3=refineLeft0 w ∧ histLeft0 3=histLeft0 w := by decide +kernel
lemma refineLeft0_iff_4 : ∀ w, refineLeft1 4=refineLeft1 w ↔ refineLeft0 4=refineLeft0 w ∧ histLeft0 4=histLeft0 w := by decide +kernel
lemma refineLeft0_iff_5 : ∀ w, refineLeft1 5=refineLeft1 w ↔ refineLeft0 5=refineLeft0 w ∧ histLeft0 5=histLeft0 w := by decide +kernel
lemma refineLeft0_iff_6 : ∀ w, refineLeft1 6=refineLeft1 w ↔ refineLeft0 6=refineLeft0 w ∧ histLeft0 6=histLeft0 w := by decide +kernel
lemma refineLeft0_iff_7 : ∀ w, refineLeft1 7=refineLeft1 w ↔ refineLeft0 7=refineLeft0 w ∧ histLeft0 7=histLeft0 w := by decide +kernel
lemma refineLeft0_iff_8 : ∀ w, refineLeft1 8=refineLeft1 w ↔ refineLeft0 8=refineLeft0 w ∧ histLeft0 8=histLeft0 w := by decide +kernel
lemma refineLeft0_iff_9 : ∀ w, refineLeft1 9=refineLeft1 w ↔ refineLeft0 9=refineLeft0 w ∧ histLeft0 9=histLeft0 w := by decide +kernel
lemma refineLeft0_iff_10 : ∀ w, refineLeft1 10=refineLeft1 w ↔ refineLeft0 10=refineLeft0 w ∧ histLeft0 10=histLeft0 w := by decide +kernel
lemma refineLeft0_iff_11 : ∀ w, refineLeft1 11=refineLeft1 w ↔ refineLeft0 11=refineLeft0 w ∧ histLeft0 11=histLeft0 w := by decide +kernel
lemma refineLeft0_iff_12 : ∀ w, refineLeft1 12=refineLeft1 w ↔ refineLeft0 12=refineLeft0 w ∧ histLeft0 12=histLeft0 w := by decide +kernel
lemma refineLeft0_iff : ∀ v w, refineLeft1 v=refineLeft1 w ↔ refineLeft0 v=refineLeft0 w ∧ histLeft0 v=histLeft0 w := by
  intro v; fin_cases v
  · exact refineLeft0_iff_0
  · exact refineLeft0_iff_1
  · exact refineLeft0_iff_2
  · exact refineLeft0_iff_3
  · exact refineLeft0_iff_4
  · exact refineLeft0_iff_5
  · exact refineLeft0_iff_6
  · exact refineLeft0_iff_7
  · exact refineLeft0_iff_8
  · exact refineLeft0_iff_9
  · exact refineLeft0_iff_10
  · exact refineLeft0_iff_11
  · exact refineLeft0_iff_12
def histRight0 : Fin 22 → Fin 35 → ℕ := ![![3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]
lemma histRight0_0 : ∀ c, neighborHistogram (fun k : ActCorner => k.1) (fun k : ActCorner => refineLeft0 (cornerPoint k)) 0 c=histRight0 0 c := by decide +kernel
lemma histRight0_1 : ∀ c, neighborHistogram (fun k : ActCorner => k.1) (fun k : ActCorner => refineLeft0 (cornerPoint k)) 1 c=histRight0 1 c := by decide +kernel
lemma histRight0_2 : ∀ c, neighborHistogram (fun k : ActCorner => k.1) (fun k : ActCorner => refineLeft0 (cornerPoint k)) 2 c=histRight0 2 c := by decide +kernel
lemma histRight0_3 : ∀ c, neighborHistogram (fun k : ActCorner => k.1) (fun k : ActCorner => refineLeft0 (cornerPoint k)) 3 c=histRight0 3 c := by decide +kernel
lemma histRight0_4 : ∀ c, neighborHistogram (fun k : ActCorner => k.1) (fun k : ActCorner => refineLeft0 (cornerPoint k)) 4 c=histRight0 4 c := by decide +kernel
lemma histRight0_5 : ∀ c, neighborHistogram (fun k : ActCorner => k.1) (fun k : ActCorner => refineLeft0 (cornerPoint k)) 5 c=histRight0 5 c := by decide +kernel
lemma histRight0_6 : ∀ c, neighborHistogram (fun k : ActCorner => k.1) (fun k : ActCorner => refineLeft0 (cornerPoint k)) 6 c=histRight0 6 c := by decide +kernel
lemma histRight0_7 : ∀ c, neighborHistogram (fun k : ActCorner => k.1) (fun k : ActCorner => refineLeft0 (cornerPoint k)) 7 c=histRight0 7 c := by decide +kernel
lemma histRight0_8 : ∀ c, neighborHistogram (fun k : ActCorner => k.1) (fun k : ActCorner => refineLeft0 (cornerPoint k)) 8 c=histRight0 8 c := by decide +kernel
lemma histRight0_9 : ∀ c, neighborHistogram (fun k : ActCorner => k.1) (fun k : ActCorner => refineLeft0 (cornerPoint k)) 9 c=histRight0 9 c := by decide +kernel
lemma histRight0_10 : ∀ c, neighborHistogram (fun k : ActCorner => k.1) (fun k : ActCorner => refineLeft0 (cornerPoint k)) 10 c=histRight0 10 c := by decide +kernel
lemma histRight0_11 : ∀ c, neighborHistogram (fun k : ActCorner => k.1) (fun k : ActCorner => refineLeft0 (cornerPoint k)) 11 c=histRight0 11 c := by decide +kernel
lemma histRight0_12 : ∀ c, neighborHistogram (fun k : ActCorner => k.1) (fun k : ActCorner => refineLeft0 (cornerPoint k)) 12 c=histRight0 12 c := by decide +kernel
lemma histRight0_13 : ∀ c, neighborHistogram (fun k : ActCorner => k.1) (fun k : ActCorner => refineLeft0 (cornerPoint k)) 13 c=histRight0 13 c := by decide +kernel
lemma histRight0_14 : ∀ c, neighborHistogram (fun k : ActCorner => k.1) (fun k : ActCorner => refineLeft0 (cornerPoint k)) 14 c=histRight0 14 c := by decide +kernel
lemma histRight0_15 : ∀ c, neighborHistogram (fun k : ActCorner => k.1) (fun k : ActCorner => refineLeft0 (cornerPoint k)) 15 c=histRight0 15 c := by decide +kernel
lemma histRight0_16 : ∀ c, neighborHistogram (fun k : ActCorner => k.1) (fun k : ActCorner => refineLeft0 (cornerPoint k)) 16 c=histRight0 16 c := by decide +kernel
lemma histRight0_17 : ∀ c, neighborHistogram (fun k : ActCorner => k.1) (fun k : ActCorner => refineLeft0 (cornerPoint k)) 17 c=histRight0 17 c := by decide +kernel
lemma histRight0_18 : ∀ c, neighborHistogram (fun k : ActCorner => k.1) (fun k : ActCorner => refineLeft0 (cornerPoint k)) 18 c=histRight0 18 c := by decide +kernel
lemma histRight0_19 : ∀ c, neighborHistogram (fun k : ActCorner => k.1) (fun k : ActCorner => refineLeft0 (cornerPoint k)) 19 c=histRight0 19 c := by decide +kernel
lemma histRight0_20 : ∀ c, neighborHistogram (fun k : ActCorner => k.1) (fun k : ActCorner => refineLeft0 (cornerPoint k)) 20 c=histRight0 20 c := by decide +kernel
lemma histRight0_21 : ∀ c, neighborHistogram (fun k : ActCorner => k.1) (fun k : ActCorner => refineLeft0 (cornerPoint k)) 21 c=histRight0 21 c := by decide +kernel
lemma histRight0_correct : ∀ v c, neighborHistogram (fun k : ActCorner => k.1) (fun k : ActCorner => refineLeft0 (cornerPoint k)) v c=histRight0 v c := by
  intro v; fin_cases v
  · exact histRight0_0
  · exact histRight0_1
  · exact histRight0_2
  · exact histRight0_3
  · exact histRight0_4
  · exact histRight0_5
  · exact histRight0_6
  · exact histRight0_7
  · exact histRight0_8
  · exact histRight0_9
  · exact histRight0_10
  · exact histRight0_11
  · exact histRight0_12
  · exact histRight0_13
  · exact histRight0_14
  · exact histRight0_15
  · exact histRight0_16
  · exact histRight0_17
  · exact histRight0_18
  · exact histRight0_19
  · exact histRight0_20
  · exact histRight0_21
lemma refineRight0_iff_0 : ∀ w, refineRight1 0=refineRight1 w ↔ refineRight0 0=refineRight0 w ∧ histRight0 0=histRight0 w := by decide +kernel
lemma refineRight0_iff_1 : ∀ w, refineRight1 1=refineRight1 w ↔ refineRight0 1=refineRight0 w ∧ histRight0 1=histRight0 w := by decide +kernel
lemma refineRight0_iff_2 : ∀ w, refineRight1 2=refineRight1 w ↔ refineRight0 2=refineRight0 w ∧ histRight0 2=histRight0 w := by decide +kernel
lemma refineRight0_iff_3 : ∀ w, refineRight1 3=refineRight1 w ↔ refineRight0 3=refineRight0 w ∧ histRight0 3=histRight0 w := by decide +kernel
lemma refineRight0_iff_4 : ∀ w, refineRight1 4=refineRight1 w ↔ refineRight0 4=refineRight0 w ∧ histRight0 4=histRight0 w := by decide +kernel
lemma refineRight0_iff_5 : ∀ w, refineRight1 5=refineRight1 w ↔ refineRight0 5=refineRight0 w ∧ histRight0 5=histRight0 w := by decide +kernel
lemma refineRight0_iff_6 : ∀ w, refineRight1 6=refineRight1 w ↔ refineRight0 6=refineRight0 w ∧ histRight0 6=histRight0 w := by decide +kernel
lemma refineRight0_iff_7 : ∀ w, refineRight1 7=refineRight1 w ↔ refineRight0 7=refineRight0 w ∧ histRight0 7=histRight0 w := by decide +kernel
lemma refineRight0_iff_8 : ∀ w, refineRight1 8=refineRight1 w ↔ refineRight0 8=refineRight0 w ∧ histRight0 8=histRight0 w := by decide +kernel
lemma refineRight0_iff_9 : ∀ w, refineRight1 9=refineRight1 w ↔ refineRight0 9=refineRight0 w ∧ histRight0 9=histRight0 w := by decide +kernel
lemma refineRight0_iff_10 : ∀ w, refineRight1 10=refineRight1 w ↔ refineRight0 10=refineRight0 w ∧ histRight0 10=histRight0 w := by decide +kernel
lemma refineRight0_iff_11 : ∀ w, refineRight1 11=refineRight1 w ↔ refineRight0 11=refineRight0 w ∧ histRight0 11=histRight0 w := by decide +kernel
lemma refineRight0_iff_12 : ∀ w, refineRight1 12=refineRight1 w ↔ refineRight0 12=refineRight0 w ∧ histRight0 12=histRight0 w := by decide +kernel
lemma refineRight0_iff_13 : ∀ w, refineRight1 13=refineRight1 w ↔ refineRight0 13=refineRight0 w ∧ histRight0 13=histRight0 w := by decide +kernel
lemma refineRight0_iff_14 : ∀ w, refineRight1 14=refineRight1 w ↔ refineRight0 14=refineRight0 w ∧ histRight0 14=histRight0 w := by decide +kernel
lemma refineRight0_iff_15 : ∀ w, refineRight1 15=refineRight1 w ↔ refineRight0 15=refineRight0 w ∧ histRight0 15=histRight0 w := by decide +kernel
lemma refineRight0_iff_16 : ∀ w, refineRight1 16=refineRight1 w ↔ refineRight0 16=refineRight0 w ∧ histRight0 16=histRight0 w := by decide +kernel
lemma refineRight0_iff_17 : ∀ w, refineRight1 17=refineRight1 w ↔ refineRight0 17=refineRight0 w ∧ histRight0 17=histRight0 w := by decide +kernel
lemma refineRight0_iff_18 : ∀ w, refineRight1 18=refineRight1 w ↔ refineRight0 18=refineRight0 w ∧ histRight0 18=histRight0 w := by decide +kernel
lemma refineRight0_iff_19 : ∀ w, refineRight1 19=refineRight1 w ↔ refineRight0 19=refineRight0 w ∧ histRight0 19=histRight0 w := by decide +kernel
lemma refineRight0_iff_20 : ∀ w, refineRight1 20=refineRight1 w ↔ refineRight0 20=refineRight0 w ∧ histRight0 20=histRight0 w := by decide +kernel
lemma refineRight0_iff_21 : ∀ w, refineRight1 21=refineRight1 w ↔ refineRight0 21=refineRight0 w ∧ histRight0 21=histRight0 w := by decide +kernel
lemma refineRight0_iff : ∀ v w, refineRight1 v=refineRight1 w ↔ refineRight0 v=refineRight0 w ∧ histRight0 v=histRight0 w := by
  intro v; fin_cases v
  · exact refineRight0_iff_0
  · exact refineRight0_iff_1
  · exact refineRight0_iff_2
  · exact refineRight0_iff_3
  · exact refineRight0_iff_4
  · exact refineRight0_iff_5
  · exact refineRight0_iff_6
  · exact refineRight0_iff_7
  · exact refineRight0_iff_8
  · exact refineRight0_iff_9
  · exact refineRight0_iff_10
  · exact refineRight0_iff_11
  · exact refineRight0_iff_12
  · exact refineRight0_iff_13
  · exact refineRight0_iff_14
  · exact refineRight0_iff_15
  · exact refineRight0_iff_16
  · exact refineRight0_iff_17
  · exact refineRight0_iff_18
  · exact refineRight0_iff_19
  · exact refineRight0_iff_20
  · exact refineRight0_iff_21
end OAI.SidorenkoCounterexample
open OAI.SidorenkoCounterexample

theorem solution :
  (∀ v w : Fin 13, refineLeft1 v = refineLeft1 w ↔
    refineLeft0 v = refineLeft0 w ∧
    neighborHistogram cornerPoint (fun k : ActCorner => refineRight0 k.1) v =
      neighborHistogram cornerPoint (fun k : ActCorner => refineRight0 k.1) w) ∧
  (∀ v w : Fin 22, refineRight1 v = refineRight1 w ↔
    refineRight0 v = refineRight0 w ∧
    neighborHistogram (fun k : ActCorner => k.1) (fun k => refineLeft0 (cornerPoint k)) v =
      neighborHistogram (fun k : ActCorner => k.1) (fun k => refineLeft0 (cornerPoint k)) w) := by
  have hL : neighborHistogram cornerPoint (fun k : ActCorner => refineRight0 k.1) = histLeft0 := by
    funext v c
    exact histLeft0_correct v c
  have hR : neighborHistogram (fun k : ActCorner => k.1) (fun k => refineLeft0 (cornerPoint k)) = histRight0 := by
    funext v c
    exact histRight0_correct v c
  have hl : (∀ v w : Fin 13, refineLeft1 v = refineLeft1 w ↔
    refineLeft0 v = refineLeft0 w ∧
    neighborHistogram cornerPoint (fun k : ActCorner => refineRight0 k.1) v =
      neighborHistogram cornerPoint (fun k : ActCorner => refineRight0 k.1) w) := by
    simpa only [hL] using refineLeft0_iff
  have hr : (∀ v w : Fin 22, refineRight1 v = refineRight1 w ↔
    refineRight0 v = refineRight0 w ∧
    neighborHistogram (fun k : ActCorner => k.1) (fun k => refineLeft0 (cornerPoint k)) v =
      neighborHistogram (fun k : ActCorner => k.1) (fun k => refineLeft0 (cornerPoint k)) w) := by
    simpa only [hR] using refineRight0_iff
  exact ⟨hl, hr⟩

