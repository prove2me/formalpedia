-- Prove2me | solution 1 for OAI.TreeEdit.BinaryLower.exists_normalized_embedding
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T18:26:43.291902+00:00
-- url     : https://prove2.me/submissions/1495b9ef-9d61-4fa1-8996-aeb866997008

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

open OAI OAI.TreeEdit OAI.TreeEdit.BinaryLower
open scoped ENNReal
variable {X Y : Type*}


theorem solution [Finite X] [Nontrivial X]
    (ρ : X → X → ℝ) (hρ : ∀ x y, 0 ≤ ρ x y)
    (hdiag : ∀ x, ρ x x = 0) (hpos : ∀ x y, x ≠ y → 0 < ρ x y)
    (f : X → RealL1) (hf : Function.Injective f) :
    ∃ g : X → RealL1, Function.Injective g ∧
      ∀ x y, ρ x y ≤ ‖g x - g y‖ ∧ ‖g x - g y‖ ≤ distortion ρ f * ρ x y := by
  set S1 := sSup {r : ℝ | ∃ x y : X, x ≠ y ∧ r = ‖f x - f y‖ / ρ x y} with hS1
  set S2 := sSup {r : ℝ | ∃ x y : X, x ≠ y ∧ r = ρ x y / ‖f x - f y‖} with hS2
  have hb1 : BddAbove {r : ℝ | ∃ x y : X, x ≠ y ∧ r = ‖f x - f y‖ / ρ x y} := by
    refine ((Set.finite_range (fun p : X × X => ‖f p.1 - f p.2‖ / ρ p.1 p.2)).subset ?_).bddAbove
    rintro r ⟨x, y, -, rfl⟩; exact ⟨(x, y), rfl⟩
  have hb2 : BddAbove {r : ℝ | ∃ x y : X, x ≠ y ∧ r = ρ x y / ‖f x - f y‖} := by
    refine ((Set.finite_range (fun p : X × X => ρ p.1 p.2 / ‖f p.1 - f p.2‖)).subset ?_).bddAbove
    rintro r ⟨x, y, -, rfl⟩; exact ⟨(x, y), rfl⟩
  have hnorm : ∀ x y, x ≠ y → 0 < ‖f x - f y‖ := fun x y h =>
    norm_pos_iff.2 (sub_ne_zero.2 (hf.ne h))
  have h1 : ∀ x y, x ≠ y → ‖f x - f y‖ / ρ x y ≤ S1 := fun x y h => le_csSup hb1 ⟨x, y, h, rfl⟩
  have h2 : ∀ x y, x ≠ y → ρ x y / ‖f x - f y‖ ≤ S2 := fun x y h => le_csSup hb2 ⟨x, y, h, rfl⟩
  obtain ⟨x0, y0, hxy0⟩ := exists_pair_ne X
  have hS2pos : 0 < S2 := lt_of_lt_of_le (div_pos (hpos x0 y0 hxy0) (hnorm x0 y0 hxy0)) (h2 x0 y0 hxy0)
  refine ⟨fun x => S2 • f x, ?_, ?_⟩
  · intro x y hxy
    exact hf (smul_right_injective _ hS2pos.ne' hxy)
  · intro x y
    have hd : ‖S2 • f x - S2 • f y‖ = S2 * ‖f x - f y‖ := by
      rw [← smul_sub, norm_smul, Real.norm_of_nonneg hS2pos.le]
    rw [hd]
    by_cases hxy : x = y
    · subst hxy; simp [hdiag]
    have hn := hnorm x y hxy
    have hp := hpos x y hxy
    have a1 := h1 x y hxy
    have a2 := h2 x y hxy
    rw [div_le_iff₀ hp] at a1
    rw [div_le_iff₀ hn] at a2
    have : distortion ρ f = S1 * S2 := rfl
    rw [this]
    constructor
    · linarith
    · nlinarith

