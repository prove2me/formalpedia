-- Prove2me | solution 2 for OAI.TreeEdit.BinaryLower.SegmentCode.SegmentSeparated.lcs_le
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T21:08:33.002275+00:00
-- url     : https://prove2.me/submissions/f29a873b-ecd3-4d2d-9ca9-86e7424ca900

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/BinaryEdit/SegmentCodeLCS.lean:L21-L40
-- (upload_full_project.md Phase 4): solution for node OAI.TreeEdit.BinaryLower.SegmentCode.SegmentSeparated.lcs_le. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
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

-- ---- from OAI.Combinatorics.TreeEdit.Alignments ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

namespace TreeEdit

universe u

variable {α : Type u} {x y z : List α}

namespace Alignment

variable {n : ℕ}

end Alignment

theorem exists_lcs_alignment (x y : List α) : Nonempty (Alignment x y (lcs x y)) := by
  obtain ⟨z, hx, hy, hz⟩ := exists_lcs x y
  obtain ⟨f, hf⟩ := List.sublist_iff_exists_fin_orderEmbedding_get_eq.mp hx
  obtain ⟨g, hg⟩ := List.sublist_iff_exists_fin_orderEmbedding_get_eq.mp hy
  refine ⟨⟨(Fin.castOrderIso hz.symm).toOrderEmbedding.comp f,
    (Fin.castOrderIso hz.symm).toOrderEmbedding.comp g, ?_⟩⟩
  intro i
  exact (hf (Fin.cast hz.symm i)).symm.trans (hg (Fin.cast hz.symm i))

end TreeEdit

end OAI

-- ---- from OAI.Combinatorics.BinaryEdit.SegmentCodeLCS ----
namespace OAI

namespace TreeEdit.BinaryLower.SegmentCode
open RandomMatching

/-- Array windows coincide with actual contiguous list segments. -/
theorem ofFn_window {α : Type*} {P : ℕ} (b : Fin P → α)
    (a i : ℕ) (hi : i+a ≤ P) :
    List.ofFn (fun t : Fin a => b (window a i hi t)) =
      ((List.ofFn b).drop i).take a := by
  apply List.ext_getElem
  · simp only [List.length_ofFn, List.length_take, List.length_drop]
    omega
  · intro j hj hj'
    simp only [List.getElem_ofFn, List.getElem_take, List.getElem_drop]
    rfl

/-- The simultaneous increasing-matching property bounds the actual LCS of
contiguous codeword segments. -/
theorem SegmentSeparated.lcs_le {K P a₀ : ℕ} {c : Fin K → Fin P → Bool}
    (hc : SegmentSeparated c a₀) (k l : Fin K) (hkl : k ≠ l)
    (a i j : ℕ) (ha : a₀ ≤ a) (hi : i+a ≤ P) (hj : j+a ≤ P) :
    100 * lcs (((List.ofFn (c k)).drop i).take a)
      (((List.ofFn (c l)).drop j).take a) ≤ 99*a := by
  rw [← ofFn_window (c k) a i hi, ← ofFn_window (c l) a j hj]
  let x := List.ofFn (fun t : Fin a => c k (window a i hi t))
  let y := List.ofFn (fun t : Fin a => c l (window a j hj t))
  have hx : x.length = a := by simp [x]
  have hy : y.length = a := by simp [y]
  obtain ⟨⟨f, g, hfg⟩⟩ := exists_lcs_alignment x y
  let f' : IncreasingPositions a (lcs x y) :=
    ⟨fun t => Fin.cast hx (f t), (Fin.cast_strictMono hx).comp f.strictMono⟩
  let g' : IncreasingPositions a (lcs x y) :=
    ⟨fun t => Fin.cast hy (g t), (Fin.cast_strictMono hy).comp g.strictMono⟩
  apply hc k l hkl a i j ha hi hj (lcs x y) f' g'
  intro t
  simpa [x, y, f', g', Fin.cast] using hfg t

end TreeEdit.BinaryLower.SegmentCode

end OAI

-- ---- platform node ----
open OAI OAI.TreeEdit OAI.TreeEdit.BinaryLower OAI.TreeEdit.BinaryLower.SegmentCode
open RandomMatching


theorem solution : type_of% @_root_.OAI.TreeEdit.BinaryLower.SegmentCode.SegmentSeparated.lcs_le := @_root_.OAI.TreeEdit.BinaryLower.SegmentCode.SegmentSeparated.lcs_le
