-- Prove2me | solution 2 for OAI.TreeEdit.BinaryLower.ParameterImage.exists_word_image_lower
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T20:06:42.560776+00:00
-- url     : https://prove2.me/submissions/b44a521d-ab9b-4835-8c87-32eadc8a4755

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/BinaryEdit/ParameterImage.lean:L59-L83
-- (upload_full_project.md Phase 4): solution for node OAI.TreeEdit.BinaryLower.ParameterImage.exists_word_image_lower. The node keeps its source
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
import Theorems.Thm_OAI_TreeEdit_BinaryLower_ParameterImage_image_lower_of_nonexpanding_obstruction

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

-- ---- from OAI.Combinatorics.BinaryEdit.ParameterImage ----
namespace OAI

/-! Lower distortion bounds on the finite image of a parameter space. -/

noncomputable section
namespace TreeEdit.BinaryLower.ParameterImage

variable {A X : Type*} [Fintype A]

/-- The finite-image obstruction for ordinary edit distance on fixed-length words. -/
theorem exists_word_image_lower {Γ : Type*} {n : ℕ}
    (G : A → Word Γ n)
    (hsep : ∃ a b, 0 < ed (G a).val (G b).val)
    (D : ℝ)
    (hobstruction : ∀ (F : A → RealL1) (C : ℝ), 0 < C →
      (∀ a b, (ed (G a).val (G b).val : ℝ) / C ≤ ‖F a - F b‖ ∧
        ‖F a - F b‖ ≤ (ed (G a).val (G b).val : ℝ)) → D ≤ C) :
    ∃ W : Finset (Word Γ n),
      (∀ w, w ∈ W ↔ ∃ a, G a = w) ∧ 2 ≤ W.card ∧
      D ≤ c1 {w : Word Γ n // w ∈ W}
        (fun x y => (ed x.val.val y.val.val : ℝ)) := by
  have hG : ∃ a b, G a ≠ G b := by
    obtain ⟨a, b, hab⟩ := hsep
    refine ⟨a, b, ?_⟩
    intro h
    rw [h, ed_self] at hab
    omega
  have h := image_lower_of_nonexpanding_obstruction G hG
    (fun x y : Word Γ n => (ed x.val y.val : ℝ))
    (fun _ _ => Nat.cast_nonneg _) (fun _ => by simp)
    (fun x y hxy => by
      exact_mod_cast (editDistance_pos_iff.mpr (fun h => hxy (Subtype.ext h))))
    D hobstruction
  exact ⟨image G, mem_image G, h.1, h.2⟩

end TreeEdit.BinaryLower.ParameterImage

end

end OAI

-- ---- platform node ----
open OAI OAI.TreeEdit OAI.TreeEdit.BinaryLower OAI.TreeEdit.BinaryLower.ParameterImage


theorem solution : type_of% @_root_.OAI.TreeEdit.BinaryLower.ParameterImage.exists_word_image_lower := @_root_.OAI.TreeEdit.BinaryLower.ParameterImage.exists_word_image_lower
