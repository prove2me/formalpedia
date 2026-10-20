-- Prove2me | solution 1 for OAI.TreeEdit.BinaryLower.SegmentCode.SegmentSeparated.lcs_le
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T18:22:38.586281+00:00
-- url     : https://prove2.me/submissions/2a4916e3-5277-40dd-affa-11dfee5fb1a7

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

open OAI OAI.TreeEdit OAI.TreeEdit.BinaryLower OAI.TreeEdit.BinaryLower.SegmentCode
open RandomMatching
theorem h49_win_len {P : ℕ} (x : Fin P → Bool) (a i : ℕ) (hi : i + a ≤ P) :
    (((List.ofFn x).drop i).take a).length = a := by
  simp; omega

theorem h49_win_get {P : ℕ} (x : Fin P → Bool) (a i : ℕ) (hi : i + a ≤ P) (t : Fin a) (h) :
    (((List.ofFn x).drop i).take a).get ⟨t.val, h⟩ = x (window a i hi t) := by
  simp [window]

theorem solution {K P a₀ : ℕ} {c : Fin K → Fin P → Bool}
    (hc : SegmentSeparated c a₀) (k l : Fin K) (hkl : k ≠ l)
    (a i j : ℕ) (ha : a₀ ≤ a) (hi : i+a ≤ P) (hj : j+a ≤ P) :
    100 * lcs (((List.ofFn (c k)).drop i).take a)
      (((List.ofFn (c l)).drop j).take a) ≤ 99*a := by
  obtain ⟨z, hzx, hzy, hzl⟩ := exists_lcs (((List.ofFn (c k)).drop i).take a)
      (((List.ofFn (c l)).drop j).take a)
  rw [← hzl]
  obtain ⟨F, hF⟩ := List.sublist_iff_exists_fin_orderEmbedding_get_eq.mp hzx
  obtain ⟨G, hG⟩ := List.sublist_iff_exists_fin_orderEmbedding_get_eq.mp hzy
  have lx := h49_win_len (c k) a i hi
  have ly := h49_win_len (c l) a j hj
  let f : IncreasingPositions a z.length :=
    ⟨fun t => ⟨(F t).val, by have := (F t).isLt; omega⟩, fun s t h => by
      have := F.strictMono h; exact this⟩
  let g : IncreasingPositions a z.length :=
    ⟨fun t => ⟨(G t).val, by have := (G t).isLt; omega⟩, fun s t h => by
      have := G.strictMono h; exact this⟩
  apply hc k l hkl a i j ha hi hj z.length f g
  intro t
  have e1 := hF t
  have e2 := hG t
  rw [← h49_win_get (c k) a i hi (f.1 t) (F t).isLt, ← h49_win_get (c l) a j hj (g.1 t) (G t).isLt]
  exact e1.symm.trans e2

