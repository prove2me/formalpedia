-- Prove2me | solution 1 for OAI.TreeEdit.BinaryLower.c1_le_bilip_mul
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T19:57:20.693094+00:00
-- url     : https://prove2.me/submissions/c9a5d81e-0d6a-4976-a6b5-3514843adcfc

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/BinaryEdit/Distortion.lean:L253-L274
-- (upload_full_project.md Phase 4): solution for node OAI.TreeEdit.BinaryLower.c1_le_bilip_mul. The node keeps its source
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
import Theorems.Thm_OAI_TreeEdit_BinaryLower_distortion_comp_le_bilip

-- ---- from OAI.Combinatorics.BinaryEdit.Distortion ----
namespace OAI

/-! Distortion of finite metric spaces under injective maps into real ℓ₁. -/

noncomputable section
open scoped ENNReal

namespace TreeEdit.BinaryLower

variable {X Y : Type*}

lemma expansionRatios_finite [Finite X] (ρ : X → X → ℝ) (f : X → RealL1) :
    (expansionRatios ρ f).Finite := by
  apply Set.Finite.subset (Set.finite_range (fun p : X × X => ‖f p.1 - f p.2‖ / ρ p.1 p.2))
  rintro r ⟨x, y, _, rfl⟩
  exact ⟨(x, y), rfl⟩

lemma contractionRatios_finite [Finite X] (ρ : X → X → ℝ) (f : X → RealL1) :
    (contractionRatios ρ f).Finite := by
  apply Set.Finite.subset (Set.finite_range (fun p : X × X => ρ p.1 p.2 / ‖f p.1 - f p.2‖))
  rintro r ⟨x, y, _, rfl⟩
  exact ⟨(x, y), rfl⟩

lemma expansion_nonneg [Finite X] [Nontrivial X] (ρ : X → X → ℝ)
    (hρ : ∀ x y, 0 ≤ ρ x y) (f : X → RealL1) :
    0 ≤ sSup (expansionRatios ρ f) := by
  obtain ⟨x, y, hxy⟩ := exists_pair_ne X
  exact (div_nonneg (norm_nonneg _) (hρ x y)).trans
    (le_csSup (expansionRatios_finite ρ f).bddAbove ⟨x, y, hxy, rfl⟩)

lemma contraction_nonneg [Finite X] [Nontrivial X] (ρ : X → X → ℝ)
    (hρ : ∀ x y, 0 ≤ ρ x y) (f : X → RealL1) :
    0 ≤ sSup (contractionRatios ρ f) := by
  obtain ⟨x, y, hxy⟩ := exists_pair_ne X
  exact (div_nonneg (hρ x y) (norm_nonneg _)).trans
    (le_csSup (contractionRatios_finite ρ f).bddAbove ⟨x, y, hxy, rfl⟩)

lemma distortion_nonneg [Finite X] [Nontrivial X] (ρ : X → X → ℝ)
    (hρ : ∀ x y, 0 ≤ ρ x y) (f : X → RealL1) : 0 ≤ distortion ρ f :=
  mul_nonneg (expansion_nonneg ρ hρ f) (contraction_nonneg ρ hρ f)

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

lemma embeddingDistortions_bddBelow [Finite X] [Nontrivial X]
    (ρ : X → X → ℝ) (hρ : ∀ x y, 0 ≤ ρ x y) :
    BddBelow (embeddingDistortions ρ) := by
  refine ⟨0, ?_⟩
  rintro D ⟨f, _, rfl⟩
  exact distortion_nonneg ρ hρ f

lemma c1_le_distortion [Finite X] [Nontrivial X]
    (ρ : X → X → ℝ) (hρ : ∀ x y, 0 ≤ ρ x y)
    (f : X → RealL1) (hf : Function.Injective f) : c1 X ρ ≤ distortion ρ f := by
  exact csInf_le (embeddingDistortions_bddBelow ρ hρ) ⟨f, hf, rfl⟩

lemma le_c1 [Finite X] (ρ : X → X → ℝ) (D : ℝ)
    (h : ∀ f : X → RealL1, Function.Injective f → D ≤ distortion ρ f) :
    D ≤ c1 X ρ := by
  apply le_csInf (embeddingDistortions_nonempty ρ)
  rintro e ⟨f, hf, rfl⟩
  exact h f hf

/-- Optimal distortion transfer through any scaled bi-Lipschitz injection.
In particular, `a=P/804` and `b=P` give constant distortion loss. -/
lemma c1_le_bilip_mul [Finite X] [Nontrivial X] [Finite Y] [Nontrivial Y]
    (ρ : X → X → ℝ) (σ : Y → Y → ℝ)
    (hρ : ∀ x y, 0 ≤ ρ x y) (hσ : ∀ x y, 0 ≤ σ x y)
    (hpos : ∀ x y, x ≠ y → 0 < ρ x y)
    (g : X → Y) (hg : Function.Injective g)
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hlower : ∀ x y, a * ρ x y ≤ σ (g x) (g y))
    (hupper : ∀ x y, σ (g x) (g y) ≤ b * ρ x y) :
    c1 X ρ ≤ (b / a) * c1 Y σ := by
  have hba : 0 < b / a := div_pos hb ha
  have h : c1 X ρ / (b / a) ≤ c1 Y σ := by
    apply le_c1
    intro f hf
    apply (div_le_iff₀ hba).2
    calc
      c1 X ρ ≤ distortion ρ (f ∘ g) := c1_le_distortion ρ hρ (f ∘ g) (hf.comp hg)
      _ ≤ (b / a) * distortion σ f :=
        distortion_comp_le_bilip ρ σ hρ hσ hpos g hg a b ha hb.le hlower hupper f
      _ = distortion σ f * (b / a) := mul_comm _ _
  simpa [mul_comm] using (div_le_iff₀ hba).1 h

end TreeEdit.BinaryLower

end

end OAI

-- ---- platform node ----
open OAI OAI.TreeEdit OAI.TreeEdit.BinaryLower
open scoped ENNReal


theorem solution : type_of% @_root_.OAI.TreeEdit.BinaryLower.c1_le_bilip_mul := @_root_.OAI.TreeEdit.BinaryLower.c1_le_bilip_mul
