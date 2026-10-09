-- Prove2me | solution 1 for OAI.SidorenkoCounterexample.refinement_round_3
-- status  : ACCEPTED   (prove)
-- author  : @abcdefg
-- created : 2026-10-08T17:27:43.641703+00:00
-- url     : https://prove2.me/submissions/55d56d4e-6cd8-40b8-8132-66e8cae29207

import Mathlib
import Definitions.Def_SidorenkoRefinementColors
namespace OAI.SidorenkoCounterexample
open scoped BigOperators
def histLeft3 : Fin 13 → Fin 35 → ℕ := ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 2, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 2, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]
lemma histLeft3_0 : ∀ c, neighborHistogram cornerPoint (fun k : ActCorner => refineRight3 k.1) 0 c=histLeft3 0 c := by decide +kernel
lemma histLeft3_1 : ∀ c, neighborHistogram cornerPoint (fun k : ActCorner => refineRight3 k.1) 1 c=histLeft3 1 c := by decide +kernel
lemma histLeft3_2 : ∀ c, neighborHistogram cornerPoint (fun k : ActCorner => refineRight3 k.1) 2 c=histLeft3 2 c := by decide +kernel
lemma histLeft3_3 : ∀ c, neighborHistogram cornerPoint (fun k : ActCorner => refineRight3 k.1) 3 c=histLeft3 3 c := by decide +kernel
lemma histLeft3_4 : ∀ c, neighborHistogram cornerPoint (fun k : ActCorner => refineRight3 k.1) 4 c=histLeft3 4 c := by decide +kernel
lemma histLeft3_5 : ∀ c, neighborHistogram cornerPoint (fun k : ActCorner => refineRight3 k.1) 5 c=histLeft3 5 c := by decide +kernel
lemma histLeft3_6 : ∀ c, neighborHistogram cornerPoint (fun k : ActCorner => refineRight3 k.1) 6 c=histLeft3 6 c := by decide +kernel
lemma histLeft3_7 : ∀ c, neighborHistogram cornerPoint (fun k : ActCorner => refineRight3 k.1) 7 c=histLeft3 7 c := by decide +kernel
lemma histLeft3_8 : ∀ c, neighborHistogram cornerPoint (fun k : ActCorner => refineRight3 k.1) 8 c=histLeft3 8 c := by decide +kernel
lemma histLeft3_9 : ∀ c, neighborHistogram cornerPoint (fun k : ActCorner => refineRight3 k.1) 9 c=histLeft3 9 c := by decide +kernel
lemma histLeft3_10 : ∀ c, neighborHistogram cornerPoint (fun k : ActCorner => refineRight3 k.1) 10 c=histLeft3 10 c := by decide +kernel
lemma histLeft3_11 : ∀ c, neighborHistogram cornerPoint (fun k : ActCorner => refineRight3 k.1) 11 c=histLeft3 11 c := by decide +kernel
lemma histLeft3_12 : ∀ c, neighborHistogram cornerPoint (fun k : ActCorner => refineRight3 k.1) 12 c=histLeft3 12 c := by decide +kernel
lemma histLeft3_correct : ∀ v c, neighborHistogram cornerPoint (fun k : ActCorner => refineRight3 k.1) v c=histLeft3 v c := by
  intro v; fin_cases v
  · exact histLeft3_0
  · exact histLeft3_1
  · exact histLeft3_2
  · exact histLeft3_3
  · exact histLeft3_4
  · exact histLeft3_5
  · exact histLeft3_6
  · exact histLeft3_7
  · exact histLeft3_8
  · exact histLeft3_9
  · exact histLeft3_10
  · exact histLeft3_11
  · exact histLeft3_12
lemma refineLeft3_iff_0 : ∀ w, refineLeft4 0=refineLeft4 w ↔ refineLeft3 0=refineLeft3 w ∧ histLeft3 0=histLeft3 w := by decide +kernel
lemma refineLeft3_iff_1 : ∀ w, refineLeft4 1=refineLeft4 w ↔ refineLeft3 1=refineLeft3 w ∧ histLeft3 1=histLeft3 w := by decide +kernel
lemma refineLeft3_iff_2 : ∀ w, refineLeft4 2=refineLeft4 w ↔ refineLeft3 2=refineLeft3 w ∧ histLeft3 2=histLeft3 w := by decide +kernel
lemma refineLeft3_iff_3 : ∀ w, refineLeft4 3=refineLeft4 w ↔ refineLeft3 3=refineLeft3 w ∧ histLeft3 3=histLeft3 w := by decide +kernel
lemma refineLeft3_iff_4 : ∀ w, refineLeft4 4=refineLeft4 w ↔ refineLeft3 4=refineLeft3 w ∧ histLeft3 4=histLeft3 w := by decide +kernel
lemma refineLeft3_iff_5 : ∀ w, refineLeft4 5=refineLeft4 w ↔ refineLeft3 5=refineLeft3 w ∧ histLeft3 5=histLeft3 w := by decide +kernel
lemma refineLeft3_iff_6 : ∀ w, refineLeft4 6=refineLeft4 w ↔ refineLeft3 6=refineLeft3 w ∧ histLeft3 6=histLeft3 w := by decide +kernel
lemma refineLeft3_iff_7 : ∀ w, refineLeft4 7=refineLeft4 w ↔ refineLeft3 7=refineLeft3 w ∧ histLeft3 7=histLeft3 w := by decide +kernel
lemma refineLeft3_iff_8 : ∀ w, refineLeft4 8=refineLeft4 w ↔ refineLeft3 8=refineLeft3 w ∧ histLeft3 8=histLeft3 w := by decide +kernel
lemma refineLeft3_iff_9 : ∀ w, refineLeft4 9=refineLeft4 w ↔ refineLeft3 9=refineLeft3 w ∧ histLeft3 9=histLeft3 w := by decide +kernel
lemma refineLeft3_iff_10 : ∀ w, refineLeft4 10=refineLeft4 w ↔ refineLeft3 10=refineLeft3 w ∧ histLeft3 10=histLeft3 w := by decide +kernel
lemma refineLeft3_iff_11 : ∀ w, refineLeft4 11=refineLeft4 w ↔ refineLeft3 11=refineLeft3 w ∧ histLeft3 11=histLeft3 w := by decide +kernel
lemma refineLeft3_iff_12 : ∀ w, refineLeft4 12=refineLeft4 w ↔ refineLeft3 12=refineLeft3 w ∧ histLeft3 12=histLeft3 w := by decide +kernel
lemma refineLeft3_iff : ∀ v w, refineLeft4 v=refineLeft4 w ↔ refineLeft3 v=refineLeft3 w ∧ histLeft3 v=histLeft3 w := by
  intro v; fin_cases v
  · exact refineLeft3_iff_0
  · exact refineLeft3_iff_1
  · exact refineLeft3_iff_2
  · exact refineLeft3_iff_3
  · exact refineLeft3_iff_4
  · exact refineLeft3_iff_5
  · exact refineLeft3_iff_6
  · exact refineLeft3_iff_7
  · exact refineLeft3_iff_8
  · exact refineLeft3_iff_9
  · exact refineLeft3_iff_10
  · exact refineLeft3_iff_11
  · exact refineLeft3_iff_12
def histRight3 : Fin 22 → Fin 35 → ℕ := ![![0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]
lemma histRight3_0 : ∀ c, neighborHistogram (fun k : ActCorner => k.1) (fun k : ActCorner => refineLeft3 (cornerPoint k)) 0 c=histRight3 0 c := by decide +kernel
lemma histRight3_1 : ∀ c, neighborHistogram (fun k : ActCorner => k.1) (fun k : ActCorner => refineLeft3 (cornerPoint k)) 1 c=histRight3 1 c := by decide +kernel
lemma histRight3_2 : ∀ c, neighborHistogram (fun k : ActCorner => k.1) (fun k : ActCorner => refineLeft3 (cornerPoint k)) 2 c=histRight3 2 c := by decide +kernel
lemma histRight3_3 : ∀ c, neighborHistogram (fun k : ActCorner => k.1) (fun k : ActCorner => refineLeft3 (cornerPoint k)) 3 c=histRight3 3 c := by decide +kernel
lemma histRight3_4 : ∀ c, neighborHistogram (fun k : ActCorner => k.1) (fun k : ActCorner => refineLeft3 (cornerPoint k)) 4 c=histRight3 4 c := by decide +kernel
lemma histRight3_5 : ∀ c, neighborHistogram (fun k : ActCorner => k.1) (fun k : ActCorner => refineLeft3 (cornerPoint k)) 5 c=histRight3 5 c := by decide +kernel
lemma histRight3_6 : ∀ c, neighborHistogram (fun k : ActCorner => k.1) (fun k : ActCorner => refineLeft3 (cornerPoint k)) 6 c=histRight3 6 c := by decide +kernel
lemma histRight3_7 : ∀ c, neighborHistogram (fun k : ActCorner => k.1) (fun k : ActCorner => refineLeft3 (cornerPoint k)) 7 c=histRight3 7 c := by decide +kernel
lemma histRight3_8 : ∀ c, neighborHistogram (fun k : ActCorner => k.1) (fun k : ActCorner => refineLeft3 (cornerPoint k)) 8 c=histRight3 8 c := by decide +kernel
lemma histRight3_9 : ∀ c, neighborHistogram (fun k : ActCorner => k.1) (fun k : ActCorner => refineLeft3 (cornerPoint k)) 9 c=histRight3 9 c := by decide +kernel
lemma histRight3_10 : ∀ c, neighborHistogram (fun k : ActCorner => k.1) (fun k : ActCorner => refineLeft3 (cornerPoint k)) 10 c=histRight3 10 c := by decide +kernel
lemma histRight3_11 : ∀ c, neighborHistogram (fun k : ActCorner => k.1) (fun k : ActCorner => refineLeft3 (cornerPoint k)) 11 c=histRight3 11 c := by decide +kernel
lemma histRight3_12 : ∀ c, neighborHistogram (fun k : ActCorner => k.1) (fun k : ActCorner => refineLeft3 (cornerPoint k)) 12 c=histRight3 12 c := by decide +kernel
lemma histRight3_13 : ∀ c, neighborHistogram (fun k : ActCorner => k.1) (fun k : ActCorner => refineLeft3 (cornerPoint k)) 13 c=histRight3 13 c := by decide +kernel
lemma histRight3_14 : ∀ c, neighborHistogram (fun k : ActCorner => k.1) (fun k : ActCorner => refineLeft3 (cornerPoint k)) 14 c=histRight3 14 c := by decide +kernel
lemma histRight3_15 : ∀ c, neighborHistogram (fun k : ActCorner => k.1) (fun k : ActCorner => refineLeft3 (cornerPoint k)) 15 c=histRight3 15 c := by decide +kernel
lemma histRight3_16 : ∀ c, neighborHistogram (fun k : ActCorner => k.1) (fun k : ActCorner => refineLeft3 (cornerPoint k)) 16 c=histRight3 16 c := by decide +kernel
lemma histRight3_17 : ∀ c, neighborHistogram (fun k : ActCorner => k.1) (fun k : ActCorner => refineLeft3 (cornerPoint k)) 17 c=histRight3 17 c := by decide +kernel
lemma histRight3_18 : ∀ c, neighborHistogram (fun k : ActCorner => k.1) (fun k : ActCorner => refineLeft3 (cornerPoint k)) 18 c=histRight3 18 c := by decide +kernel
lemma histRight3_19 : ∀ c, neighborHistogram (fun k : ActCorner => k.1) (fun k : ActCorner => refineLeft3 (cornerPoint k)) 19 c=histRight3 19 c := by decide +kernel
lemma histRight3_20 : ∀ c, neighborHistogram (fun k : ActCorner => k.1) (fun k : ActCorner => refineLeft3 (cornerPoint k)) 20 c=histRight3 20 c := by decide +kernel
lemma histRight3_21 : ∀ c, neighborHistogram (fun k : ActCorner => k.1) (fun k : ActCorner => refineLeft3 (cornerPoint k)) 21 c=histRight3 21 c := by decide +kernel
lemma histRight3_correct : ∀ v c, neighborHistogram (fun k : ActCorner => k.1) (fun k : ActCorner => refineLeft3 (cornerPoint k)) v c=histRight3 v c := by
  intro v; fin_cases v
  · exact histRight3_0
  · exact histRight3_1
  · exact histRight3_2
  · exact histRight3_3
  · exact histRight3_4
  · exact histRight3_5
  · exact histRight3_6
  · exact histRight3_7
  · exact histRight3_8
  · exact histRight3_9
  · exact histRight3_10
  · exact histRight3_11
  · exact histRight3_12
  · exact histRight3_13
  · exact histRight3_14
  · exact histRight3_15
  · exact histRight3_16
  · exact histRight3_17
  · exact histRight3_18
  · exact histRight3_19
  · exact histRight3_20
  · exact histRight3_21
lemma refineRight3_iff_0 : ∀ w, refineRight4 0=refineRight4 w ↔ refineRight3 0=refineRight3 w ∧ histRight3 0=histRight3 w := by decide +kernel
lemma refineRight3_iff_1 : ∀ w, refineRight4 1=refineRight4 w ↔ refineRight3 1=refineRight3 w ∧ histRight3 1=histRight3 w := by decide +kernel
lemma refineRight3_iff_2 : ∀ w, refineRight4 2=refineRight4 w ↔ refineRight3 2=refineRight3 w ∧ histRight3 2=histRight3 w := by decide +kernel
lemma refineRight3_iff_3 : ∀ w, refineRight4 3=refineRight4 w ↔ refineRight3 3=refineRight3 w ∧ histRight3 3=histRight3 w := by decide +kernel
lemma refineRight3_iff_4 : ∀ w, refineRight4 4=refineRight4 w ↔ refineRight3 4=refineRight3 w ∧ histRight3 4=histRight3 w := by decide +kernel
lemma refineRight3_iff_5 : ∀ w, refineRight4 5=refineRight4 w ↔ refineRight3 5=refineRight3 w ∧ histRight3 5=histRight3 w := by decide +kernel
lemma refineRight3_iff_6 : ∀ w, refineRight4 6=refineRight4 w ↔ refineRight3 6=refineRight3 w ∧ histRight3 6=histRight3 w := by decide +kernel
lemma refineRight3_iff_7 : ∀ w, refineRight4 7=refineRight4 w ↔ refineRight3 7=refineRight3 w ∧ histRight3 7=histRight3 w := by decide +kernel
lemma refineRight3_iff_8 : ∀ w, refineRight4 8=refineRight4 w ↔ refineRight3 8=refineRight3 w ∧ histRight3 8=histRight3 w := by decide +kernel
lemma refineRight3_iff_9 : ∀ w, refineRight4 9=refineRight4 w ↔ refineRight3 9=refineRight3 w ∧ histRight3 9=histRight3 w := by decide +kernel
lemma refineRight3_iff_10 : ∀ w, refineRight4 10=refineRight4 w ↔ refineRight3 10=refineRight3 w ∧ histRight3 10=histRight3 w := by decide +kernel
lemma refineRight3_iff_11 : ∀ w, refineRight4 11=refineRight4 w ↔ refineRight3 11=refineRight3 w ∧ histRight3 11=histRight3 w := by decide +kernel
lemma refineRight3_iff_12 : ∀ w, refineRight4 12=refineRight4 w ↔ refineRight3 12=refineRight3 w ∧ histRight3 12=histRight3 w := by decide +kernel
lemma refineRight3_iff_13 : ∀ w, refineRight4 13=refineRight4 w ↔ refineRight3 13=refineRight3 w ∧ histRight3 13=histRight3 w := by decide +kernel
lemma refineRight3_iff_14 : ∀ w, refineRight4 14=refineRight4 w ↔ refineRight3 14=refineRight3 w ∧ histRight3 14=histRight3 w := by decide +kernel
lemma refineRight3_iff_15 : ∀ w, refineRight4 15=refineRight4 w ↔ refineRight3 15=refineRight3 w ∧ histRight3 15=histRight3 w := by decide +kernel
lemma refineRight3_iff_16 : ∀ w, refineRight4 16=refineRight4 w ↔ refineRight3 16=refineRight3 w ∧ histRight3 16=histRight3 w := by decide +kernel
lemma refineRight3_iff_17 : ∀ w, refineRight4 17=refineRight4 w ↔ refineRight3 17=refineRight3 w ∧ histRight3 17=histRight3 w := by decide +kernel
lemma refineRight3_iff_18 : ∀ w, refineRight4 18=refineRight4 w ↔ refineRight3 18=refineRight3 w ∧ histRight3 18=histRight3 w := by decide +kernel
lemma refineRight3_iff_19 : ∀ w, refineRight4 19=refineRight4 w ↔ refineRight3 19=refineRight3 w ∧ histRight3 19=histRight3 w := by decide +kernel
lemma refineRight3_iff_20 : ∀ w, refineRight4 20=refineRight4 w ↔ refineRight3 20=refineRight3 w ∧ histRight3 20=histRight3 w := by decide +kernel
lemma refineRight3_iff_21 : ∀ w, refineRight4 21=refineRight4 w ↔ refineRight3 21=refineRight3 w ∧ histRight3 21=histRight3 w := by decide +kernel
lemma refineRight3_iff : ∀ v w, refineRight4 v=refineRight4 w ↔ refineRight3 v=refineRight3 w ∧ histRight3 v=histRight3 w := by
  intro v; fin_cases v
  · exact refineRight3_iff_0
  · exact refineRight3_iff_1
  · exact refineRight3_iff_2
  · exact refineRight3_iff_3
  · exact refineRight3_iff_4
  · exact refineRight3_iff_5
  · exact refineRight3_iff_6
  · exact refineRight3_iff_7
  · exact refineRight3_iff_8
  · exact refineRight3_iff_9
  · exact refineRight3_iff_10
  · exact refineRight3_iff_11
  · exact refineRight3_iff_12
  · exact refineRight3_iff_13
  · exact refineRight3_iff_14
  · exact refineRight3_iff_15
  · exact refineRight3_iff_16
  · exact refineRight3_iff_17
  · exact refineRight3_iff_18
  · exact refineRight3_iff_19
  · exact refineRight3_iff_20
  · exact refineRight3_iff_21
lemma refineLeft_final : Function.Injective refineLeft4 := by decide +kernel
lemma refineRight_final : Function.Injective refineRight4 := by decide +kernel
end OAI.SidorenkoCounterexample
open OAI.SidorenkoCounterexample

theorem solution :
  (∀ v w : Fin 13, refineLeft4 v = refineLeft4 w ↔
    refineLeft3 v = refineLeft3 w ∧
    neighborHistogram cornerPoint (fun k : ActCorner => refineRight3 k.1) v =
      neighborHistogram cornerPoint (fun k : ActCorner => refineRight3 k.1) w) ∧
  (∀ v w : Fin 22, refineRight4 v = refineRight4 w ↔
    refineRight3 v = refineRight3 w ∧
    neighborHistogram (fun k : ActCorner => k.1) (fun k => refineLeft3 (cornerPoint k)) v =
      neighborHistogram (fun k : ActCorner => k.1) (fun k => refineLeft3 (cornerPoint k)) w) ∧
  Function.Injective refineLeft4 ∧ Function.Injective refineRight4 := by
  have hL : neighborHistogram cornerPoint (fun k : ActCorner => refineRight3 k.1) = histLeft3 := by
    funext v c
    exact histLeft3_correct v c
  have hR : neighborHistogram (fun k : ActCorner => k.1) (fun k => refineLeft3 (cornerPoint k)) = histRight3 := by
    funext v c
    exact histRight3_correct v c
  have hl : (∀ v w : Fin 13, refineLeft4 v = refineLeft4 w ↔
    refineLeft3 v = refineLeft3 w ∧
    neighborHistogram cornerPoint (fun k : ActCorner => refineRight3 k.1) v =
      neighborHistogram cornerPoint (fun k : ActCorner => refineRight3 k.1) w) := by
    simpa only [hL] using refineLeft3_iff
  have hr : (∀ v w : Fin 22, refineRight4 v = refineRight4 w ↔
    refineRight3 v = refineRight3 w ∧
    neighborHistogram (fun k : ActCorner => k.1) (fun k => refineLeft3 (cornerPoint k)) v =
      neighborHistogram (fun k : ActCorner => k.1) (fun k => refineLeft3 (cornerPoint k)) w) := by
    simpa only [hR] using refineRight3_iff
  exact ⟨hl, hr, refineLeft_final, refineRight_final⟩

