-- Prove2me | solution 1 for OAI.TreeEdit.BinaryLower.exists_nonexpanding_embedding
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T18:23:45.408839+00:00
-- url     : https://prove2.me/submissions/59b2af75-d4dc-4947-8d42-376ecd1a7a23

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
    0 < distortion ρ f ∧ ∃ g : X → RealL1, Function.Injective g ∧
      ∀ x y, ρ x y / distortion ρ f ≤ ‖g x - g y‖ ∧ ‖g x - g y‖ ≤ ρ x y := by
  classical
  have _ := Fintype.ofFinite X
  set E := sSup {r : ℝ | ∃ x y : X, x ≠ y ∧ r = ‖f x - f y‖ / ρ x y} with hE
  set C := sSup {r : ℝ | ∃ x y : X, x ≠ y ∧ r = ρ x y / ‖f x - f y‖} with hC
  have hbE : BddAbove {r : ℝ | ∃ x y : X, x ≠ y ∧ r = ‖f x - f y‖ / ρ x y} := by
    apply Set.Finite.bddAbove
    apply (Set.finite_range (fun p : X × X => ‖f p.1 - f p.2‖ / ρ p.1 p.2)).subset
    rintro r ⟨x, y, _, rfl⟩; exact ⟨(x, y), rfl⟩
  have hbC : BddAbove {r : ℝ | ∃ x y : X, x ≠ y ∧ r = ρ x y / ‖f x - f y‖} := by
    apply Set.Finite.bddAbove
    apply (Set.finite_range (fun p : X × X => ρ p.1 p.2 / ‖f p.1 - f p.2‖)).subset
    rintro r ⟨x, y, _, rfl⟩; exact ⟨(x, y), rfl⟩
  have hnorm : ∀ x y, x ≠ y → 0 < ‖f x - f y‖ := fun x y h =>
    norm_pos_iff.2 (sub_ne_zero.2 (hf.ne h))
  have hEle : ∀ x y, x ≠ y → ‖f x - f y‖ / ρ x y ≤ E := fun x y h =>
    le_csSup hbE ⟨x, y, h, rfl⟩
  have hCle : ∀ x y, x ≠ y → ρ x y / ‖f x - f y‖ ≤ C := fun x y h =>
    le_csSup hbC ⟨x, y, h, rfl⟩
  obtain ⟨x0, y0, hxy0⟩ := exists_pair_ne X
  have hEpos : 0 < E := lt_of_lt_of_le (div_pos (hnorm _ _ hxy0) (hpos _ _ hxy0)) (hEle _ _ hxy0)
  have hCpos : 0 < C := lt_of_lt_of_le (div_pos (hpos _ _ hxy0) (hnorm _ _ hxy0)) (hCle _ _ hxy0)
  have hD : distortion ρ f = E * C := rfl
  refine ⟨by rw [hD]; positivity, fun x => E⁻¹ • f x, ?_, ?_⟩
  · intro x y h
    exact hf (smul_right_injective _ (inv_ne_zero hEpos.ne') h)
  · intro x y
    rw [← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hEpos), hD]
    by_cases h : x = y
    · subst h; simp [hdiag]
    have hn := hnorm x y h
    have hp := hpos x y h
    have h1 := hEle x y h
    have h2 := hCle x y h
    rw [div_le_iff₀ hp] at h1
    rw [div_le_iff₀ hn] at h2
    constructor
    · rw [div_le_iff₀ (by positivity)]
      calc ρ x y ≤ C * ‖f x - f y‖ := h2
        _ = E⁻¹ * ‖f x - f y‖ * (E * C) := by field_simp
    · rw [inv_mul_le_iff₀ hEpos]; linarith

