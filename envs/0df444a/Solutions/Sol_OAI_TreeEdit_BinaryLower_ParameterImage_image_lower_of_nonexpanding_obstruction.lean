-- Prove2me | solution 1 for OAI.TreeEdit.BinaryLower.ParameterImage.image_lower_of_nonexpanding_obstruction
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T18:27:36.968358+00:00
-- url     : https://prove2.me/submissions/51203c27-98ad-4c65-80e4-6131b3e8df8f

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


theorem solution
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
  have hcard : 2 ≤ (image G).card := by
    obtain ⟨a, b, hab⟩ := hG
    have ha : G a ∈ image G := (mem_image G _).2 ⟨a, rfl⟩
    have hb : G b ∈ image G := (mem_image G _).2 ⟨b, rfl⟩
    exact Finset.one_lt_card.2 ⟨_, ha, _, hb, hab⟩
  refine ⟨hcard, ?_⟩
  set Y := {x : X // x ∈ image G}
  set ρY : Y → Y → ℝ := fun x y => ρ x.val y.val
  -- nonempty: an injective map into ℓ¹
  have hne : {D' : ℝ | ∃ f : Y → RealL1, Function.Injective f ∧ D' = distortion ρY f}.Nonempty := by
    let e := Fintype.equivFin Y
    let f : Y → RealL1 := fun y => lp.single (E := fun _ : ℕ => ℝ) 1 ((e y : ℕ)) (1:ℝ)
    refine ⟨_, f, ?_, rfl⟩
    intro y z hyz
    by_contra hne'
    have hi : ((e y : ℕ)) ≠ ((e z : ℕ)) := by
      intro h; exact hne' (e.injective (Fin.ext h))
    have := congrArg (fun g : RealL1 => g ((e y : ℕ))) hyz
    simp only [f, lp.single_apply_self, lp.single_apply_ne _ _ _ hi] at this
    norm_num at this
  apply le_csInf hne
  rintro _ ⟨f, hf, rfl⟩
  set S1 := sSup {r : ℝ | ∃ x y : Y, x ≠ y ∧ r = ‖f x - f y‖ / ρY x y} with hS1
  set S2 := sSup {r : ℝ | ∃ x y : Y, x ≠ y ∧ r = ρY x y / ‖f x - f y‖} with hS2
  have hb1 : BddAbove {r : ℝ | ∃ x y : Y, x ≠ y ∧ r = ‖f x - f y‖ / ρY x y} := by
    refine ((Set.finite_range (fun p : Y × Y => ‖f p.1 - f p.2‖ / ρY p.1 p.2)).subset ?_).bddAbove
    rintro r ⟨x, y, -, rfl⟩; exact ⟨(x, y), rfl⟩
  have hb2 : BddAbove {r : ℝ | ∃ x y : Y, x ≠ y ∧ r = ρY x y / ‖f x - f y‖} := by
    refine ((Set.finite_range (fun p : Y × Y => ρY p.1 p.2 / ‖f p.1 - f p.2‖)).subset ?_).bddAbove
    rintro r ⟨x, y, -, rfl⟩; exact ⟨(x, y), rfl⟩
  have hnorm : ∀ x y : Y, x ≠ y → 0 < ‖f x - f y‖ := fun x y h =>
    norm_pos_iff.2 (sub_ne_zero.2 (hf.ne h))
  have hposY : ∀ x y : Y, x ≠ y → 0 < ρY x y := fun x y h =>
    hpos _ _ (fun h' => h (Subtype.ext h'))
  have h1 : ∀ x y : Y, x ≠ y → ‖f x - f y‖ / ρY x y ≤ S1 := fun x y h => le_csSup hb1 ⟨x, y, h, rfl⟩
  have h2 : ∀ x y : Y, x ≠ y → ρY x y / ‖f x - f y‖ ≤ S2 := fun x y h => le_csSup hb2 ⟨x, y, h, rfl⟩
  obtain ⟨a0, b0, hab0⟩ := hG
  let y0 : Y := toImage G a0
  let z0 : Y := toImage G b0
  have hyz0 : y0 ≠ z0 := fun h => hab0 (congrArg Subtype.val h)
  have hS1pos : 0 < S1 := lt_of_lt_of_le (div_pos (hnorm _ _ hyz0) (hposY _ _ hyz0)) (h1 _ _ hyz0)
  have hS2pos : 0 < S2 := lt_of_lt_of_le (div_pos (hposY _ _ hyz0) (hnorm _ _ hyz0)) (h2 _ _ hyz0)
  have hdist : distortion ρY f = S1 * S2 := rfl
  rw [hdist]
  apply hobstruction (fun a => S1⁻¹ • f (toImage G a)) (S1 * S2) (mul_pos hS1pos hS2pos)
  intro a b
  have hd : ‖S1⁻¹ • f (toImage G a) - S1⁻¹ • f (toImage G b)‖ = S1⁻¹ * ‖f (toImage G a) - f (toImage G b)‖ := by
    rw [← smul_sub, norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hS1pos.le)]
  rw [hd]
  by_cases hab : toImage G a = toImage G b
  · have hGab : G a = G b := congrArg Subtype.val hab
    rw [hab, hGab, hdiag]; simp
  · have hn := hnorm _ _ hab
    have hp := hposY _ _ hab
    have a1 := h1 _ _ hab
    have a2 := h2 _ _ hab
    rw [div_le_iff₀ hp] at a1
    rw [div_le_iff₀ hn] at a2
    change ρ (G a) (G b) / (S1 * S2) ≤ S1⁻¹ * ‖f (toImage G a) - f (toImage G b)‖ ∧
      S1⁻¹ * ‖f (toImage G a) - f (toImage G b)‖ ≤ ρY (toImage G a) (toImage G b)
    constructor
    · rw [div_le_iff₀ (mul_pos hS1pos hS2pos)]
      have : S1⁻¹ * ‖f (toImage G a) - f (toImage G b)‖ * (S1 * S2) = S2 * ‖f (toImage G a) - f (toImage G b)‖ := by
        field_simp
      rw [this]; exact a2
    · rw [inv_mul_le_iff₀ hS1pos]; linarith

