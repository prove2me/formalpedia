-- Prove2me | solution 2 for OAI.TreeEdit.BinaryLower.exists_normalized_embedding
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T19:59:56.422911+00:00
-- url     : https://prove2.me/submissions/5f9bcd05-b73d-4366-bc69-d15651604887

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/BinaryEdit/Distortion.lean:L276-L315
-- (upload_full_project.md Phase 4): solution for node OAI.TreeEdit.BinaryLower.exists_normalized_embedding. The node keeps its source
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

lemma contraction_nonneg [Finite X] [Nontrivial X] (ρ : X → X → ℝ)
    (hρ : ∀ x y, 0 ≤ ρ x y) (f : X → RealL1) :
    0 ≤ sSup (contractionRatios ρ f) := by
  obtain ⟨x, y, hxy⟩ := exists_pair_ne X
  exact (div_nonneg (hρ x y) (norm_nonneg _)).trans
    (le_csSup (contractionRatios_finite ρ f).bddAbove ⟨x, y, hxy, rfl⟩)

/-- Rescaling by the maximal contraction ratio makes an injective embedding
noncontracting without changing the distortion bound. -/
lemma exists_normalized_embedding [Finite X] [Nontrivial X]
    (ρ : X → X → ℝ) (hρ : ∀ x y, 0 ≤ ρ x y)
    (hdiag : ∀ x, ρ x x = 0) (hpos : ∀ x y, x ≠ y → 0 < ρ x y)
    (f : X → RealL1) (hf : Function.Injective f) :
    ∃ g : X → RealL1, Function.Injective g ∧
      ∀ x y, ρ x y ≤ ‖g x - g y‖ ∧ ‖g x - g y‖ ≤ distortion ρ f * ρ x y := by
  let C := sSup (contractionRatios ρ f)
  let E := sSup (expansionRatios ρ f)
  have hC : 0 ≤ C := contraction_nonneg ρ hρ f
  let g : X → RealL1 := fun x => C • f x
  have hnorm (x y : X) : ‖g x - g y‖ = C * ‖f x - f y‖ := by
    dsimp [g]
    rw [← smul_sub, norm_smul, Real.norm_of_nonneg hC]
  have hbounds : ∀ x y, ρ x y ≤ ‖g x - g y‖ ∧
      ‖g x - g y‖ ≤ distortion ρ f * ρ x y := by
    intro x y
    by_cases hxy : x = y
    · subst y
      simp [hdiag]
    have hr : 0 < ρ x y := hpos x y hxy
    have hn : 0 < ‖f x - f y‖ := norm_pos_iff.mpr (sub_ne_zero.mpr (fun h => hxy (hf h)))
    have hc : ρ x y / ‖f x - f y‖ ≤ C :=
      le_csSup (contractionRatios_finite ρ f).bddAbove ⟨x, y, hxy, rfl⟩
    have he : ‖f x - f y‖ / ρ x y ≤ E :=
      le_csSup (expansionRatios_finite ρ f).bddAbove ⟨x, y, hxy, rfl⟩
    constructor
    · rw [hnorm]
      exact (div_le_iff₀ hn).1 hc
    · rw [hnorm]
      have ht := mul_le_mul_of_nonneg_left ((div_le_iff₀ hr).1 he) hC
      change C * ‖f x - f y‖ ≤ (E * C) * ρ x y
      nlinarith
  refine ⟨g, ?_, hbounds⟩
  intro x y h
  by_contra hxy
  have ht := (hbounds x y).1
  rw [h, sub_self, norm_zero] at ht
  exact (not_le_of_gt (hpos x y hxy)) ht

end TreeEdit.BinaryLower

end

end OAI

-- ---- platform node ----
open OAI OAI.TreeEdit OAI.TreeEdit.BinaryLower
open scoped ENNReal


theorem solution : type_of% @_root_.OAI.TreeEdit.BinaryLower.exists_normalized_embedding := @_root_.OAI.TreeEdit.BinaryLower.exists_normalized_embedding
