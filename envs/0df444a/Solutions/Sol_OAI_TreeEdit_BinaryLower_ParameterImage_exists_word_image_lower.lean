-- Prove2me | solution 1 for OAI.TreeEdit.BinaryLower.ParameterImage.exists_word_image_lower
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T18:25:40.97367+00:00
-- url     : https://prove2.me/submissions/6b713a9d-f2e7-4730-8b5d-cfbaaacb8571

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

open OAI OAI.TreeEdit OAI.TreeEdit.BinaryLower OAI.TreeEdit.BinaryLower.ParameterImage
variable {A X : Type*} [Fintype A]
theorem h49_nonexp {X : Type*} [Finite X] [Nontrivial X]
    (ρ : X → X → ℝ) (hρ : ∀ x y, 0 ≤ ρ x y)
    (hdiag : ∀ x, ρ x x = 0) (hpos : ∀ x y, x ≠ y → 0 < ρ x y)
    (f : X → OAI.TreeEdit.RealL1) (hf : Function.Injective f) :
    0 < OAI.TreeEdit.BinaryLower.distortion ρ f ∧ ∃ g : X → OAI.TreeEdit.RealL1, Function.Injective g ∧
      ∀ x y, ρ x y / OAI.TreeEdit.BinaryLower.distortion ρ f ≤ ‖g x - g y‖ ∧ ‖g x - g y‖ ≤ ρ x y := by
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
  have hD : OAI.TreeEdit.BinaryLower.distortion ρ f = E * C := rfl
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

theorem h49_exists_inj (Y : Type*) [Finite Y] : ∃ f : Y → OAI.TreeEdit.RealL1, Function.Injective f := by
  obtain ⟨e, he⟩ := exists_injective_nat Y
  refine ⟨fun y => lp.single 1 (e y) (1:ℝ), fun y y' h => he ?_⟩
  have := congrArg (fun v : OAI.TreeEdit.RealL1 => v (e y)) h
  simp only [lp.single_apply_self] at this
  by_contra hne
  rw [lp.single_apply_ne _ _ _ hne] at this
  norm_num at this

theorem h49_c1_lower {Y : Type*} [Finite Y] [Nontrivial Y]
    (ρ : Y → Y → ℝ) (hρ : ∀ x y, 0 ≤ ρ x y)
    (hdiag : ∀ x, ρ x x = 0) (hpos : ∀ x y, x ≠ y → 0 < ρ x y) (D : ℝ)
    (h : ∀ g : Y → OAI.TreeEdit.RealL1, ∀ C : ℝ, 0 < C →
      (∀ x y, ρ x y / C ≤ ‖g x - g y‖ ∧ ‖g x - g y‖ ≤ ρ x y) → D ≤ C) :
    D ≤ OAI.TreeEdit.BinaryLower.c1 Y ρ := by
  unfold OAI.TreeEdit.BinaryLower.c1
  obtain ⟨f0, hf0⟩ := h49_exists_inj Y
  refine le_csInf ⟨OAI.TreeEdit.BinaryLower.distortion ρ f0, ⟨f0, hf0, rfl⟩⟩ ?_
  rintro _ ⟨f, hf, rfl⟩
  obtain ⟨hD, g, _, hg⟩ := h49_nonexp ρ hρ hdiag hpos f hf
  exact h g _ hD hg

theorem solution {Γ : Type*} {n : ℕ}
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
  classical
  obtain ⟨a, b, hab⟩ := hsep
  have hGab : G a ≠ G b := by
    intro h; rw [h] at hab; simp at hab
  refine ⟨image G, mem_image G, ?_, ?_⟩
  · exact Finset.one_lt_card.2 ⟨G a, (mem_image G _).2 ⟨a, rfl⟩, G b, (mem_image G _).2 ⟨b, rfl⟩, hGab⟩
  · have : Nontrivial {w : Word Γ n // w ∈ image G} :=
      ⟨⟨toImage G a, toImage G b, fun h => hGab (congrArg Subtype.val h)⟩⟩
    apply h49_c1_lower
    · intro x y; positivity
    · intro x; simp
    · intro x y hxy
      have : x.val.val ≠ y.val.val := fun h => hxy (Subtype.ext (Subtype.ext h))
      have h2 : ed x.val.val y.val.val ≠ 0 := by rwa [Ne, OAI.TreeEdit.ed_eq_zero_iff]
      positivity
    · intro g C hC hg
      exact hobstruction (fun a => g (toImage G a)) C hC (fun a b => hg (toImage G a) (toImage G b))

