-- Prove2me | solution 2 for OAI.TreeEdit.BinaryLower.c1_le_encodedSet_mul
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T20:24:34.944993+00:00
-- url     : https://prove2.me/submissions/dccb94ea-73df-428f-8d6d-1a09bb62b50d

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/BinaryEdit/EncodedImage.lean:L65-L99
-- (upload_full_project.md Phase 4): solution for node OAI.TreeEdit.BinaryLower.c1_le_encodedSet_mul. The node keeps its source
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
import Theorems.Thm_OAI_TreeEdit_BinaryLower_c1_le_bilip_mul

-- ---- from OAI.Combinatorics.BinaryEdit.EditMetric ----
namespace OAI

namespace TreeEdit.BinaryLower

universe u
variable {α : Type u}

namespace EditStep

end EditStep

namespace EditScript

end EditScript

/-- Positivity of ordinary edit distance does not require an inhabited alphabet. -/
theorem editDistance_pos_iff {x y : List α} : 0 < ed x y ↔ x ≠ y := by
  rw [Nat.pos_iff_ne_zero, ne_eq, ed_eq_zero_iff]

namespace StrictEditScript

end StrictEditScript

end TreeEdit.BinaryLower

end OAI

-- ---- from OAI.Combinatorics.BinaryEdit.EncodedImage ----
namespace OAI

/-! Distortion transport through finite images of fixed-width codes. -/

noncomputable section
namespace TreeEdit.BinaryLower

universe u

lemma encodedWord_injective_of_lower {α : Type u} {M P : ℕ}
    (c : α → Word Bool P) {a : ℝ} (ha : 0 < a)
    (hlower : ∀ x y : Word α M,
      a * (ed x.val y.val : ℝ) ≤
        (ed (encode c x.val) (encode c y.val) : ℝ)) :
    Function.Injective (encodedWord (M := M) c) := by
  intro x y hxy
  apply Subtype.ext
  apply ed_eq_zero_iff.mp
  have hval : encode c x.val = encode c y.val := congrArg Subtype.val hxy
  have h := hlower x y
  rw [hval, ed_self, Nat.cast_zero] at h
  have hed : (ed x.val y.val : ℝ) ≤ 0 := nonpos_of_mul_nonpos_right h ha
  exact Nat.eq_zero_of_le_zero (by exact_mod_cast hed)

lemma encodedMember_injective {α : Type u} {M P : ℕ}
    (c : α → Word Bool P) {a : ℝ} (ha : 0 < a)
    (hlower : ∀ x y : Word α M,
      a * (ed x.val y.val : ℝ) ≤
        (ed (encode c x.val) (encode c y.val) : ℝ))
    (W : Finset (Word α M)) : Function.Injective (encodedMember c W) := by
  intro x y hxy
  apply Subtype.ext
  apply encodedWord_injective_of_lower c ha hlower
  exact congrArg Subtype.val hxy

/-- Distortion transport for the concrete finite image of a bi-Lipschitz code. -/
lemma c1_le_encodedSet_mul {α : Type u} {M P : ℕ}
    (c : α → Word Bool P) (W : Finset (Word α M)) (hW : 2 ≤ W.card)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hlower : ∀ x y : Word α M,
      a * (ed x.val y.val : ℝ) ≤
        (ed (encode c x.val) (encode c y.val) : ℝ))
    (hupper : ∀ x y : Word α M,
      (ed (encode c x.val) (encode c y.val) : ℝ) ≤
        b * (ed x.val y.val : ℝ)) :
    c1 {x : Word α M // x ∈ W}
      (fun x y => (ed x.val.val y.val.val : ℝ)) ≤
        (b / a) * binarySetDistortion (encodedSet c W) := by
  classical
  have : Nontrivial {x : Word α M // x ∈ W} := by
    obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.mp (show 1 < W.card by omega)
    refine ⟨⟨⟨x, hx⟩, ⟨y, hy⟩, ?_⟩⟩
    exact fun h => hxy (congrArg Subtype.val h)
  have hg := encodedMember_injective c ha hlower W
  have : Nontrivial {y : Word Bool (M * P) // y ∈ encodedSet c W} := hg.nontrivial
  unfold binarySetDistortion
  refine c1_le_bilip_mul _ _ ?_ ?_ ?_ (encodedMember c W) hg a b ha hb ?_ ?_
  · intro x y
    exact Nat.cast_nonneg _
  · intro x y
    exact Nat.cast_nonneg _
  · intro x y hxy
    apply Nat.cast_pos.mpr
    apply editDistance_pos_iff.mpr
    intro h
    exact hxy (Subtype.ext (Subtype.ext h))
  · intro x y
    exact hlower x.val y.val
  · intro x y
    exact hupper x.val y.val

end TreeEdit.BinaryLower

end

end OAI

-- ---- platform node ----
open OAI OAI.TreeEdit OAI.TreeEdit.BinaryLower


theorem solution.{u} : type_of% @_root_.OAI.TreeEdit.BinaryLower.c1_le_encodedSet_mul.{u} := @_root_.OAI.TreeEdit.BinaryLower.c1_le_encodedSet_mul.{u}
