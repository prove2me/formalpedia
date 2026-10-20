-- Prove2me | solution 1 for OAI.TreeEdit.BinaryLower.common_sublist_subset_ofFn_segments
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T18:10:59.372436+00:00
-- url     : https://prove2.me/submissions/7ef6fe50-8c58-4c69-b963-73350666d394

import Mathlib
import Definitions.Def_BinaryEditLower
import Definitions.Def_OAI_Combinatorics_TreeEdit_Model__BinaryEditLower
import Definitions.Def_OAI_Combinatorics_BinaryEdit_Model
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteTreeWords
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteTreeGeometry
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteVectors
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteVectorRestrictions
import Definitions.Def_OAI_Combinatorics_BinaryEdit_WordFinite
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteTreeInstantiation
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteTreeTags
import Definitions.Def_OAI_Combinatorics_BinaryEdit_TaggedGaps
import Definitions.Def_OAI_Combinatorics_BinaryEdit_TaggedNonsplit
import Definitions.Def_OAI_Combinatorics_TreeEdit_EditMetric__BinaryEditLower
import Definitions.Def_OAI_Combinatorics_TreeEdit_Alignments__BinaryEditLower
import Definitions.Def_OAI_Combinatorics_BinaryEdit_LCS
import Definitions.Def_OAI_Combinatorics_BinaryEdit_TaggedExtraction
import Definitions.Def_OAI_Combinatorics_BinaryEdit_BlockExtraction
import Definitions.Def_OAI_Combinatorics_BinaryEdit_TaggedRowLCS
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteSeparation
import Definitions.Def_OAI_Combinatorics_BinaryEdit_Branching
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteActivityBridge
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteFourier
import Definitions.Def_OAI_Combinatorics_BinaryEdit_ScalarCutsBool
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteCoordinates
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteWordDetection
import Definitions.Def_OAI_Combinatorics_BinaryEdit_CheapTranslations
import Definitions.Def_OAI_Combinatorics_BinaryEdit_Distortion
import Definitions.Def_OAI_Combinatorics_BinaryEdit_EditMetric
import Definitions.Def_OAI_Combinatorics_BinaryEdit_ParameterImage
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteParameters
import Definitions.Def_OAI_Combinatorics_BinaryEdit_EncodedImage
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteFamilyTransfer
import Definitions.Def_OAI_Combinatorics_BinaryEdit_CodeNumerics
import Definitions.Def_OAI_Combinatorics_BinaryEdit_RandomMatching
import Definitions.Def_OAI_Combinatorics_BinaryEdit_SegmentMatchingCount
import Definitions.Def_OAI_Combinatorics_BinaryEdit_CodeUnionBound
import Definitions.Def_OAI_Combinatorics_BinaryEdit_SegmentCode
import Definitions.Def_OAI_Combinatorics_BinaryEdit_CodeAdditive
import Definitions.Def_OAI_Combinatorics_BinaryEdit_MatchingSpanBudget
import Definitions.Def_OAI_Combinatorics_BinaryEdit_MatchingSegments

open OAI OAI.TreeEdit OAI.TreeEdit.BinaryLower
theorem h49_sub_seg {α : Type*} (x : List α) {k : ℕ}
    (i : Fin k → Fin x.length) (hi : StrictMono i) (a p : ℕ)
    (hi_lo : ∀ t, a ≤ (i t : ℕ)) (hi_hi : ∀ t, (i t : ℕ) < a + p) :
    (List.ofFn (fun t => x.get (i t))).Sublist ((x.drop a).take p) := by
  rw [List.sublist_iff_exists_fin_orderEmbedding_get_eq]
  have hlen : ∀ t : Fin k, (i t : ℕ) - a < ((x.drop a).take p).length := by
    intro t; simp only [List.length_take, List.length_drop]
    have := (i t).2; have := hi_lo t; have := hi_hi t; omega
  refine ⟨OrderEmbedding.ofStrictMono
    (fun s : Fin (List.ofFn (fun t => x.get (i t))).length =>
      (⟨(i (Fin.cast (by simp) s) : ℕ) - a, hlen _⟩ : Fin ((x.drop a).take p).length)) ?_, ?_⟩
  · intro s1 s2 h
    simp only [Fin.lt_def]
    have h1 := hi (show Fin.cast (by simp) s1 < (Fin.cast (by simp) s2 : Fin k) from h)
    have := hi_lo (Fin.cast (by simp) s1); have := hi_lo (Fin.cast (by simp) s2)
    rw [Fin.lt_def] at h1; omega
  · intro s
    simp only [OrderEmbedding.coe_ofStrictMono, List.get_eq_getElem, List.getElem_ofFn,
      List.getElem_take, List.getElem_drop]
    congr 1
    have := hi_lo (Fin.cast (by simp) s)
    rw [Nat.add_sub_cancel' this]; rfl

theorem solution {α : Type*} {n m k : ℕ}
    (x : Fin n → α) (y : Fin m → α)
    (i : Fin k → Fin n) (j : Fin k → Fin m)
    (hi : StrictMono i) (hj : StrictMono j)
    (hlabel : ∀ t, x (i t) = y (j t))
    (S : Finset (Fin k)) (a b p q : ℕ)
    (hi_lo : ∀ t ∈ S, a ≤ (i t : ℕ)) (hi_hi : ∀ t ∈ S, (i t : ℕ) < a + p)
    (hj_lo : ∀ t ∈ S, b ≤ (j t : ℕ)) (hj_hi : ∀ t ∈ S, (j t : ℕ) < b + q) :
    ∃ z : List α, z.Sublist (((List.ofFn x).drop a).take p) ∧
      z.Sublist (((List.ofFn y).drop b).take q) ∧ z.length = S.card := by
  let e := S.orderEmbOfFin rfl
  let i' : Fin S.card → Fin (List.ofFn x).length := fun s => Fin.cast (by simp) (i (e s))
  let j' : Fin S.card → Fin (List.ofFn y).length := fun s => Fin.cast (by simp) (j (e s))
  have hi' : StrictMono i' := fun s1 s2 h => by
    have := hi (e.strictMono h); exact this
  have hj' : StrictMono j' := fun s1 s2 h => by
    have := hj (e.strictMono h); exact this
  have hmem : ∀ s, e s ∈ S := fun s => S.orderEmbOfFin_mem rfl s
  refine ⟨List.ofFn (fun t => (List.ofFn x).get (i' t)),
    h49_sub_seg (List.ofFn x) i' hi' a p (fun t => hi_lo _ (hmem t)) (fun t => hi_hi _ (hmem t)), ?_, by simp⟩
  have : (fun t => (List.ofFn x).get (i' t)) = (fun t => (List.ofFn y).get (j' t)) := by
    funext t; simp [i', j', hlabel]
  rw [this]
  exact h49_sub_seg (List.ofFn y) j' hj' b q (fun t => hj_lo _ (hmem t)) (fun t => hj_hi _ (hmem t))

