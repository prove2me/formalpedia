-- Prove2me | solution 2 for OAI.TreeEdit.BinaryLower.ParameterImage.exists_word_image_lower_of_root_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T20:08:59.675119+00:00
-- url     : https://prove2.me/submissions/01377287-6550-48ef-baf7-cc1bbb374949

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/BinaryEdit/ParameterImage.lean:L97-L135
-- (upload_full_project.md Phase 4): solution for node OAI.TreeEdit.BinaryLower.ParameterImage.exists_word_image_lower_of_root_bound. The node keeps its source
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
import Theorems.Thm_OAI_TreeEdit_BinaryLower_ParameterImage_exists_word_image_lower

-- ---- from OAI.Combinatorics.BinaryEdit.ParameterImage ----
namespace OAI

/-! Lower distortion bounds on the finite image of a parameter space. -/

noncomputable section
namespace TreeEdit.BinaryLower.ParameterImage

variable {A X : Type*} [Fintype A]

/-- Final finite-tree passage: the distinguished root displacement is far
in every state, but every nonexpanding ℓ₁ map has a small average root
 displacement. The resulting lower bound concerns the actual word image. -/
theorem exists_word_image_lower_of_root_bound {Γ : Type*} {n : ℕ}
    [AddCommGroup A] (G : A → Word Γ n) (z : A)
    (lower upper : ℝ) (hlower : 0 < lower) (hupper : 0 < upper)
    (hsep : ∀ x, lower ≤ (ed (G x).val (G (x + z)).val : ℝ))
    (hroot : ∀ F : A → RealL1,
      (∀ x y, ‖F x - F y‖ ≤ (ed (G x).val (G y).val : ℝ)) →
      (∑ x : A, ‖F (x + z) - F x‖) / Fintype.card A ≤ upper) :
    ∃ W : Finset (Word Γ n),
      (∀ w, w ∈ W ↔ ∃ a, G a = w) ∧ 2 ≤ W.card ∧
      lower / upper ≤ c1 {w : Word Γ n // w ∈ W}
        (fun x y => (ed x.val.val y.val.val : ℝ)) := by
  apply exists_word_image_lower G
  · refine ⟨0, z, ?_⟩
    have h := hlower.trans_le (hsep 0)
    simp only [zero_add] at h
    exact_mod_cast h
  · intro F C hC hF
    have hcard : (0 : ℝ) < Fintype.card A := by
      exact_mod_cast (Fintype.card_pos : 0 < Fintype.card A)
    have hl : ∀ x, lower / C ≤ ‖F (x + z) - F x‖ := by
      intro x
      calc
        lower / C ≤ (ed (G x).val (G (x + z)).val : ℝ) / C :=
          div_le_div_of_nonneg_right (hsep x) hC.le
        _ ≤ ‖F x - F (x + z)‖ := (hF x (x + z)).1
        _ = ‖F (x + z) - F x‖ := norm_sub_rev _ _
    have havg : lower / C ≤
        (∑ x : A, ‖F (x + z) - F x‖) / Fintype.card A := by
      apply (le_div_iff₀ hcard).2
      calc
        lower / C * (Fintype.card A : ℝ) = ∑ _x : A, lower / C := by
          simp [mul_comm]
        _ ≤ ∑ x : A, ‖F (x + z) - F x‖ := Finset.sum_le_sum (fun x _ => hl x)
    have hb : lower / C ≤ upper := havg.trans (hroot F (fun x y => (hF x y).2))
    apply (div_le_iff₀ hupper).2
    simpa only [mul_comm] using (div_le_iff₀ hC).1 hb

end TreeEdit.BinaryLower.ParameterImage

end

end OAI

-- ---- platform node ----
open OAI OAI.TreeEdit OAI.TreeEdit.BinaryLower OAI.TreeEdit.BinaryLower.ParameterImage


theorem solution : type_of% @_root_.OAI.TreeEdit.BinaryLower.ParameterImage.exists_word_image_lower_of_root_bound := @_root_.OAI.TreeEdit.BinaryLower.ParameterImage.exists_word_image_lower_of_root_bound
