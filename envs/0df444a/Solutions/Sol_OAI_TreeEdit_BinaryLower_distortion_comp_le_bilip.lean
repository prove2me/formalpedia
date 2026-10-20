-- Prove2me | solution 1 for OAI.TreeEdit.BinaryLower.distortion_comp_le_bilip
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T19:55:39.126463+00:00
-- url     : https://prove2.me/submissions/94700da5-630c-49e3-b073-52c78985e8e8

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/BinaryEdit/Distortion.lean:L197-L251
-- (upload_full_project.md Phase 4): solution for node OAI.TreeEdit.BinaryLower.distortion_comp_le_bilip. The node keeps its source
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

lemma expansionRatios_nonempty [Nontrivial X] (ρ : X → X → ℝ) (f : X → RealL1) :
    (expansionRatios ρ f).Nonempty := by
  obtain ⟨x, y, hxy⟩ := exists_pair_ne X
  exact ⟨_, x, y, hxy, rfl⟩

lemma contractionRatios_nonempty [Nontrivial X] (ρ : X → X → ℝ) (f : X → RealL1) :
    (contractionRatios ρ f).Nonempty := by
  obtain ⟨x, y, hxy⟩ := exists_pair_ne X
  exact ⟨_, x, y, hxy, rfl⟩

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

/-- Comparing two metrics through a scaled bi-Lipschitz injection costs only
its ratio of expansion to contraction in the distortion product. -/
lemma distortion_comp_le_bilip [Finite X] [Nontrivial X] [Finite Y] [Nontrivial Y]
    (ρ : X → X → ℝ) (σ : Y → Y → ℝ)
    (hρ : ∀ x y, 0 ≤ ρ x y) (hσ : ∀ x y, 0 ≤ σ x y)
    (hpos : ∀ x y, x ≠ y → 0 < ρ x y)
    (g : X → Y) (hg : Function.Injective g)
    (a b : ℝ) (ha : 0 < a) (hb : 0 ≤ b)
    (hlower : ∀ x y, a * ρ x y ≤ σ (g x) (g y))
    (hupper : ∀ x y, σ (g x) (g y) ≤ b * ρ x y) (f : Y → RealL1) :
    distortion ρ (f ∘ g) ≤ (b / a) * distortion σ f := by
  have he : sSup (expansionRatios ρ (f ∘ g)) ≤ b * sSup (expansionRatios σ f) := by
    apply csSup_le (expansionRatios_nonempty ρ (f ∘ g))
    rintro r ⟨x, y, hxy, rfl⟩
    have ht := hpos x y hxy
    have hs : 0 < σ (g x) (g y) := (mul_pos ha ht).trans_le (hlower x y)
    have hratio : ‖f (g x) - f (g y)‖ / σ (g x) (g y) ≤
        sSup (expansionRatios σ f) :=
      le_csSup (expansionRatios_finite σ f).bddAbove
        ⟨g x, g y, fun h => hxy (hg h), rfl⟩
    calc
      ‖(f ∘ g) x - (f ∘ g) y‖ / ρ x y ≤
          (b * ‖f (g x) - f (g y)‖) / σ (g x) (g y) := by
        apply (div_le_div_iff₀ ht hs).2
        have hn := norm_nonneg (f (g x) - f (g y))
        change ‖f (g x) - f (g y)‖ * σ (g x) (g y) ≤
          b * ‖f (g x) - f (g y)‖ * ρ x y
        nlinarith [mul_le_mul_of_nonneg_left (hupper x y) hn]
      _ = b * (‖f (g x) - f (g y)‖ / σ (g x) (g y)) := by ring
      _ ≤ b * sSup (expansionRatios σ f) := mul_le_mul_of_nonneg_left hratio hb
  have hc : sSup (contractionRatios ρ (f ∘ g)) ≤
      (1 / a) * sSup (contractionRatios σ f) := by
    apply csSup_le (contractionRatios_nonempty ρ (f ∘ g))
    rintro r ⟨x, y, hxy, rfl⟩
    have hratio : σ (g x) (g y) / ‖f (g x) - f (g y)‖ ≤
        sSup (contractionRatios σ f) :=
      le_csSup (contractionRatios_finite σ f).bddAbove
        ⟨g x, g y, fun h => hxy (hg h), rfl⟩
    have hmetric : ρ x y ≤ σ (g x) (g y) / a := by
      apply (le_div_iff₀ ha).2
      simpa [mul_comm] using hlower x y
    calc
      ρ x y / ‖(f ∘ g) x - (f ∘ g) y‖ ≤
          (σ (g x) (g y) / a) / ‖f (g x) - f (g y)‖ :=
        div_le_div_of_nonneg_right hmetric (norm_nonneg _)
      _ = (1 / a) * (σ (g x) (g y) / ‖f (g x) - f (g y)‖) := by ring
      _ ≤ (1 / a) * sSup (contractionRatios σ f) :=
        mul_le_mul_of_nonneg_left hratio (by positivity)
  calc
    distortion ρ (f ∘ g) ≤
        (b * sSup (expansionRatios σ f)) *
          ((1 / a) * sSup (contractionRatios σ f)) :=
      mul_le_mul he hc (contraction_nonneg ρ hρ (f ∘ g))
        (mul_nonneg hb (expansion_nonneg σ hσ f))
    _ = (b / a) * distortion σ f := by unfold distortion; unfold expansionRatios contractionRatios; ring

end TreeEdit.BinaryLower

end

end OAI

-- ---- platform node ----
open OAI OAI.TreeEdit OAI.TreeEdit.BinaryLower
open scoped ENNReal


theorem solution : type_of% @_root_.OAI.TreeEdit.BinaryLower.distortion_comp_le_bilip := @_root_.OAI.TreeEdit.BinaryLower.distortion_comp_le_bilip
