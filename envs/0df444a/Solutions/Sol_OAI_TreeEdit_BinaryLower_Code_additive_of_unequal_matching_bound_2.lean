-- Prove2me | solution 2 for OAI.TreeEdit.BinaryLower.Code.additive_of_unequal_matching_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T21:15:46.551965+00:00
-- url     : https://prove2.me/submissions/6f38eee0-8f75-4cd5-8505-00296f4761b0

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/BinaryEdit/CodeAdditive.lean:L110-L130
-- (upload_full_project.md Phase 4): solution for node OAI.TreeEdit.BinaryLower.Code.additive_of_unequal_matching_bound. The node keeps its source
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
import Definitions.Def_OAI_Combinatorics_BinaryEdit_CodeAdditive
import Theorems.Thm_OAI_TreeEdit_BinaryLower_Code_additive_of_longest_unequal_bound

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

-- ---- from OAI.Combinatorics.BinaryEdit.CodeAdditive ----
namespace OAI

/-! The longest encoded matching is partitioned by equality of its
original block labels. Segment separation and the span loss budget bound
the number of unequal-label matches. -/

namespace TreeEdit.BinaryLower.Code

universe u v

/-- An unequal count proved for every actual encoded matching yields the
source additive estimate by choosing a longest encoded matching. -/
theorem additive_of_unequal_matching_bound {α : Type u} {β : Type v}
    {M P a₀ : ℕ} (c : α → Word β P) (x y : List α)
    (hx : x.length = M) (hy : y.length = M) (hP : 0 < P)
    (hunequal : ∀ (r : ℕ) (f g : Fin r → Fin (M*P)),
      StrictMono f → StrictMono g →
      (∀ t, encodedBit c x hx (f t) = encodedBit c y hy (g t)) →
      (unequalEdges x y hx hy hP f g).card ≤ 200*(M*P-r)+2*M*a₀) :
    P*deficit M x y ≤ 201*deficit (M*P) (encode c x) (encode c y)+2*M*a₀ := by
  have hencx : (encode c x).length = M*P := by rw [length_encode, hx]
  have hency : (encode c y).length = M*P := by rw [length_encode, hy]
  obtain ⟨⟨f₀, g₀, hmatch⟩⟩ := exists_lcs_alignment (encode c x) (encode c y)
  let f := fun t => Fin.cast hencx (f₀ t)
  let g := fun t => Fin.cast hency (g₀ t)
  have hf : StrictMono f := (Fin.cast_strictMono hencx).comp f₀.strictMono
  have hg : StrictMono g := (Fin.cast_strictMono hency).comp g₀.strictMono
  apply additive_of_longest_unequal_bound c x y hx hy hP f g hf hg
  apply hunequal _ f g hf hg
  intro t
  simpa only [encodedBit, f, g, Fin.cast] using hmatch t

end TreeEdit.BinaryLower.Code

end OAI

-- ---- platform node ----
open OAI OAI.TreeEdit OAI.TreeEdit.BinaryLower OAI.TreeEdit.BinaryLower.Code


theorem solution.{u,v} : type_of% @_root_.OAI.TreeEdit.BinaryLower.Code.additive_of_unequal_matching_bound.{u,v} := @_root_.OAI.TreeEdit.BinaryLower.Code.additive_of_unequal_matching_bound.{u,v}
