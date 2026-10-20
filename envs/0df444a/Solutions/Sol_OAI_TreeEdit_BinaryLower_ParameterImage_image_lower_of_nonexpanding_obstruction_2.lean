-- Prove2me | solution 2 for OAI.TreeEdit.BinaryLower.ParameterImage.image_lower_of_nonexpanding_obstruction
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T20:04:52.336884+00:00
-- url     : https://prove2.me/submissions/88c0e7df-52e9-466b-8ce3-8a121fa3b17c

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/BinaryEdit/ParameterImage.lean:L33-L57
-- (upload_full_project.md Phase 4): solution for node OAI.TreeEdit.BinaryLower.ParameterImage.image_lower_of_nonexpanding_obstruction. The node keeps its source
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
import Theorems.Thm_OAI_TreeEdit_BinaryLower_exists_nonexpanding_embedding

-- ---- from OAI.Combinatorics.BinaryEdit.Distortion ----
namespace OAI

/-! Distortion of finite metric spaces under injective maps into real ℓ₁. -/

noncomputable section
open scoped ENNReal

namespace TreeEdit.BinaryLower

variable {X Y : Type*}

/-- Every finite set admits an injection into the full sequence space. -/
lemma exists_injective_L1 (X : Type*) [Finite X] :
    ∃ f : X → RealL1, Function.Injective f := by
  classical
  let := Fintype.ofFinite X
  let f : X → RealL1 := fun x => lp.single 1 0 ((Fintype.equivFin X x).val : ℝ)
  refine ⟨f, ?_⟩
  intro x y h
  have hv := congrArg (fun z : RealL1 => z 0) h
  simp only [f, lp.single_apply_self] at hv
  apply (Fintype.equivFin X).injective
  apply Fin.ext
  exact_mod_cast hv

lemma embeddingDistortions_nonempty [Finite X] (ρ : X → X → ℝ) :
    (embeddingDistortions ρ).Nonempty := by
  obtain ⟨f, hf⟩ := exists_injective_L1 X
  exact ⟨distortion ρ f, f, hf, rfl⟩

lemma le_c1 [Finite X] (ρ : X → X → ℝ) (D : ℝ)
    (h : ∀ f : X → RealL1, Function.Injective f → D ≤ distortion ρ f) :
    D ≤ c1 X ρ := by
  apply le_csInf (embeddingDistortions_nonempty ρ)
  rintro e ⟨f, hf, rfl⟩
  exact h f hf

lemma le_c1_of_nonexpanding [Finite X] [Nontrivial X]
    (ρ : X → X → ℝ) (hρ : ∀ x y, 0 ≤ ρ x y)
    (hdiag : ∀ x, ρ x x = 0) (hpos : ∀ x y, x ≠ y → 0 < ρ x y)
    (D : ℝ)
    (hobstruction : ∀ (g : X → RealL1) (A : ℝ), 0 < A →
      (∀ x y, ρ x y / A ≤ ‖g x - g y‖ ∧ ‖g x - g y‖ ≤ ρ x y) → D ≤ A) :
    D ≤ c1 X ρ := by
  apply le_c1
  intro f hf
  obtain ⟨hD, g, _, hg⟩ := exists_nonexpanding_embedding ρ hρ hdiag hpos f hf
  exact hobstruction g (distortion ρ f) hD hg

end TreeEdit.BinaryLower

end

end OAI

-- ---- from OAI.Combinatorics.BinaryEdit.ParameterImage ----
namespace OAI

/-! Lower distortion bounds on the finite image of a parameter space. -/

noncomputable section
namespace TreeEdit.BinaryLower.ParameterImage

variable {A X : Type*} [Fintype A]

lemma image_card_two (G : A → X) (hG : ∃ a b, G a ≠ G b) : 2 ≤ (image G).card := by
  classical
  obtain ⟨a, b, hab⟩ := hG
  apply Finset.one_lt_card.mpr
  exact ⟨G a, (mem_image G _).2 ⟨a, rfl⟩,
    G b, (mem_image G _).2 ⟨b, rfl⟩, hab⟩

/-- An obstruction for every normalized map on parameter states gives the
claimed distortion lower bound on the finite image, even when `G` is not
injective. All metric hypotheses are the ordinary ones needed to normalize. -/
theorem image_lower_of_nonexpanding_obstruction
    (G : A → X) (hG : ∃ a b, G a ≠ G b)
    (ρ : X → X → ℝ) (hρ : ∀ x y, 0 ≤ ρ x y)
    (hdiag : ∀ x, ρ x x = 0) (hpos : ∀ x y, x ≠ y → 0 < ρ x y)
    (D : ℝ)
    (hobstruction : ∀ (F : A → RealL1) (C : ℝ), 0 < C →
      (∀ a b, ρ (G a) (G b) / C ≤ ‖F a - F b‖ ∧
        ‖F a - F b‖ ≤ ρ (G a) (G b)) → D ≤ C) :
    2 ≤ (image G).card ∧
      D ≤ c1 {x : X // x ∈ image G} (fun x y => ρ x.val y.val) := by
  classical
  refine ⟨image_card_two G hG, ?_⟩
  obtain ⟨a, b, hab⟩ := hG
  let : Nontrivial {x : X // x ∈ image G} :=
    nontrivial_of_ne (toImage G a) (toImage G b)
      (fun h => hab (congrArg Subtype.val h))
  apply le_c1_of_nonexpanding (fun x y : {x : X // x ∈ image G} => ρ x.val y.val)
    (fun x y => hρ _ _) (fun x => hdiag _)
    (fun x y hxy => hpos _ _ (fun h => hxy (Subtype.ext h))) D
  intro f C hC hf
  exact hobstruction (fun a => f (toImage G a)) C hC
    (fun a b => hf (toImage G a) (toImage G b))

end TreeEdit.BinaryLower.ParameterImage

end

end OAI

-- ---- platform node ----
open OAI OAI.TreeEdit OAI.TreeEdit.BinaryLower OAI.TreeEdit.BinaryLower.ParameterImage


theorem solution : type_of% @_root_.OAI.TreeEdit.BinaryLower.ParameterImage.image_lower_of_nonexpanding_obstruction := @_root_.OAI.TreeEdit.BinaryLower.ParameterImage.image_lower_of_nonexpanding_obstruction
