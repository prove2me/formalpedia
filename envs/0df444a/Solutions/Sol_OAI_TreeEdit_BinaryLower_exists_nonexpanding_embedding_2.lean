-- Prove2me | solution 2 for OAI.TreeEdit.BinaryLower.exists_nonexpanding_embedding
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T20:02:23.060111+00:00
-- url     : https://prove2.me/submissions/2ca5ef14-d327-4331-ac6a-1dcf2af2ede3

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/BinaryEdit/Distortion.lean:L331-L363
-- (upload_full_project.md Phase 4): solution for node OAI.TreeEdit.BinaryLower.exists_nonexpanding_embedding. The node keeps its source
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
import Theorems.Thm_OAI_TreeEdit_BinaryLower_exists_normalized_embedding

-- ---- from OAI.Combinatorics.BinaryEdit.Distortion ----
namespace OAI

/-! Distortion of finite metric spaces under injective maps into real ℓ₁. -/

noncomputable section
open scoped ENNReal

namespace TreeEdit.BinaryLower

variable {X Y : Type*}

/-- The dual normalization used verbatim by the finite-tree obstruction:
the image distance lies between `ρ / distortion` and `ρ`. -/
lemma exists_nonexpanding_embedding [Finite X] [Nontrivial X]
    (ρ : X → X → ℝ) (hρ : ∀ x y, 0 ≤ ρ x y)
    (hdiag : ∀ x, ρ x x = 0) (hpos : ∀ x y, x ≠ y → 0 < ρ x y)
    (f : X → RealL1) (hf : Function.Injective f) :
    0 < distortion ρ f ∧ ∃ g : X → RealL1, Function.Injective g ∧
      ∀ x y, ρ x y / distortion ρ f ≤ ‖g x - g y‖ ∧ ‖g x - g y‖ ≤ ρ x y := by
  obtain ⟨g, _, hg⟩ := exists_normalized_embedding ρ hρ hdiag hpos f hf
  obtain ⟨x₀, y₀, hxy⟩ := exists_pair_ne X
  have hr := hpos x₀ y₀ hxy
  have hD : 0 < distortion ρ f := by
    have ht := (hg x₀ y₀).1.trans (hg x₀ y₀).2
    nlinarith
  let g' : X → RealL1 := fun x => (1 / distortion ρ f) • g x
  have hnorm (x y : X) : ‖g' x - g' y‖ = ‖g x - g y‖ / distortion ρ f := by
    dsimp [g']
    rw [← smul_sub, norm_smul, Real.norm_of_nonneg (by positivity)]
    ring
  have hb : ∀ x y, ρ x y / distortion ρ f ≤ ‖g' x - g' y‖ ∧
      ‖g' x - g' y‖ ≤ ρ x y := by
    intro x y
    rw [hnorm]
    constructor
    · exact div_le_div_of_nonneg_right (hg x y).1 hD.le
    · apply (div_le_iff₀ hD).2
      simpa [mul_comm] using (hg x y).2
  refine ⟨hD, g', ?_, hb⟩
  intro x y h
  by_contra hxy
  have ht := (hb x y).1
  rw [h, sub_self, norm_zero] at ht
  exact (not_le_of_gt (div_pos (hpos x y hxy) hD)) ht

end TreeEdit.BinaryLower

end

end OAI

-- ---- platform node ----
open OAI OAI.TreeEdit OAI.TreeEdit.BinaryLower
open scoped ENNReal


theorem solution : type_of% @_root_.OAI.TreeEdit.BinaryLower.exists_nonexpanding_embedding := @_root_.OAI.TreeEdit.BinaryLower.exists_nonexpanding_embedding
