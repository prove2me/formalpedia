-- Prove2me | solution 1 for LeanEval.Geometry.SpaceGroupsProblem.space_groups
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-09-06T05:57:35.919461+00:00
-- url     : https://prove2.me/submissions/6f7bf7ca-f0d1-44cd-b950-3874f5e4ed5d
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_LeanEval_SpaceGroups_Definitions
import Theorems.Thm_LeanEval_Geometry_SpaceGroupsProblem_space_groups_OP_classification
import Theorems.Thm_LeanEval_Geometry_SpaceGroupsProblem_space_groups_affine_classification
import Theorems.Thm_LeanEval_Geometry_SpaceGroupsProblem_space_groups_sohncke_classification

namespace SpaceGroupsReduction

open LeanEval.Geometry.SpaceGroupsProblem

/-! ### Counting equivalence classes by a complete, irredundant list of representatives -/

/-- If `r` is an equivalence relation on `α` and `f : Fin n → α` meets every `r`-class exactly
once, then the set of `r`-classes has cardinality `n`. -/
theorem encard_classes_of_reps {α : Type*} (r : α → α → Prop)
    (hrefl : ∀ a, r a a) (hsymm : ∀ a b, r a b → r b a)
    (htrans : ∀ a b c, r a b → r b c → r a c)
    {n : ℕ} (f : Fin n → α)
    (hex : ∀ a, ∃ i, r (f i) a) (hsep : ∀ i j, r (f i) (f j) → i = j) :
    Set.encard {S : Set α | ∃ a : α, S = {b | r a b}} = (n : ℕ∞) := by
  have hset : {S : Set α | ∃ a : α, S = {b | r a b}} = Set.range (fun i => {b | r (f i) b}) := by
    ext S
    constructor
    · rintro ⟨a, rfl⟩
      obtain ⟨i, hi⟩ := hex a
      refine ⟨i, ?_⟩
      ext b
      exact ⟨fun hb => htrans _ _ _ (hsymm _ _ hi) hb, fun hb => htrans _ _ _ hi hb⟩
    · rintro ⟨i, rfl⟩
      exact ⟨f i, rfl⟩
  have hinj : Function.Injective (fun i => {b | r (f i) b}) := by
    intro i j hij
    have hmem : (f j) ∈ {b | r (f i) b} := by
      simp only [Set.ext_iff] at hij
      exact (hij (f j)).2 (hrefl _)
    exact hsep _ _ hmem
  rw [hset, ← Set.image_univ, Set.InjOn.encard_image hinj.injOn, Set.encard_univ]
  simp

/-! ### Conjugation of a group of isometries by a fixed affine map -/

/-- `ConjBy φ G₁ G₂` says that conjugating `G₁` by the affine map `φ` produces exactly `G₂`. -/
def ConjBy {d : ℕ} (φ : AffineGroup d) (G₁ G₂ : Subgroup (EuclideanIsom d)) : Prop :=
  {h : AffineGroup d | ∃ g ∈ G₁, h = φ * g.toAffineEquiv * φ⁻¹} =
  {h : AffineGroup d | ∃ g ∈ G₂, h = g.toAffineEquiv}

theorem conjBy_one {d : ℕ} (G : Subgroup (EuclideanIsom d)) : ConjBy 1 G G := by
  ext h
  simp

theorem conjBy_inv {d : ℕ} {φ : AffineGroup d} {G₁ G₂ : Subgroup (EuclideanIsom d)}
    (h : ConjBy φ G₁ G₂) : ConjBy φ⁻¹ G₂ G₁ := by
  have h' := Set.ext_iff.mp h
  simp only [Set.mem_ofPred_eq] at h'
  ext x
  simp only [Set.mem_ofPred_eq]
  constructor
  · rintro ⟨g₂, hg₂, rfl⟩
    obtain ⟨g₁, hg₁, hgg⟩ := (h' (g₂.toAffineEquiv)).2 ⟨g₂, hg₂, rfl⟩
    refine ⟨g₁, hg₁, ?_⟩
    rw [hgg]
    group
  · rintro ⟨g₁, hg₁, rfl⟩
    obtain ⟨g₂, hg₂, hgg⟩ := (h' (φ * g₁.toAffineEquiv * φ⁻¹)).1 ⟨g₁, hg₁, rfl⟩
    refine ⟨g₂, hg₂, ?_⟩
    rw [← hgg]
    group

theorem conjBy_trans {d : ℕ} {φ ψ : AffineGroup d} {G₁ G₂ G₃ : Subgroup (EuclideanIsom d)}
    (h₁ : ConjBy φ G₁ G₂) (h₂ : ConjBy ψ G₂ G₃) : ConjBy (ψ * φ) G₁ G₃ := by
  have h₁' := Set.ext_iff.mp h₁
  have h₂' := Set.ext_iff.mp h₂
  simp only [Set.mem_ofPred_eq] at h₁' h₂'
  ext x
  simp only [Set.mem_ofPred_eq]
  constructor
  · rintro ⟨g₁, hg₁, rfl⟩
    obtain ⟨g₂, hg₂, hgg⟩ := (h₁' (φ * g₁.toAffineEquiv * φ⁻¹)).1 ⟨g₁, hg₁, rfl⟩
    obtain ⟨g₃, hg₃, hgg'⟩ := (h₂' (ψ * g₂.toAffineEquiv * ψ⁻¹)).1 ⟨g₂, hg₂, rfl⟩
    refine ⟨g₃, hg₃, ?_⟩
    rw [← hgg', ← hgg]
    group
  · rintro ⟨g₃, hg₃, rfl⟩
    obtain ⟨g₂, hg₂, hgg⟩ := (h₂' (g₃.toAffineEquiv)).2 ⟨g₃, hg₃, rfl⟩
    obtain ⟨g₁, hg₁, hgg'⟩ := (h₁' (g₂.toAffineEquiv)).2 ⟨g₂, hg₂, rfl⟩
    refine ⟨g₁, hg₁, ?_⟩
    rw [hgg, hgg']
    group

/-! ### Determinants of the linear parts -/

theorem affine_det_mul {d : ℕ} (φ ψ : AffineGroup d) :
    ((φ * ψ).linear.det : ℝ) = (φ.linear.det : ℝ) * (ψ.linear.det : ℝ) := by
  have h : (φ * ψ).linear = φ.linear * ψ.linear := LinearEquiv.toLinearMap_inj.mp rfl
  rw [h]
  simp only [LinearEquiv.coe_det]
  rw [show ((φ.linear * ψ.linear : E d ≃ₗ[ℝ] E d) : E d →ₗ[ℝ] E d)
      = (φ.linear : E d →ₗ[ℝ] E d) ∘ₗ (ψ.linear : E d →ₗ[ℝ] E d) from rfl]
  exact LinearMap.det_comp _ _

theorem affine_det_one (d : ℕ) : (((1 : AffineGroup d).linear.det : ℝ)) = 1 := by
  have h : ((1 : AffineGroup d).linear) = 1 := LinearEquiv.toLinearMap_inj.mp rfl
  rw [h]
  simp

theorem affine_det_inv_pos {d : ℕ} {φ : AffineGroup d} (h : 0 < (φ.linear.det : ℝ)) :
    0 < ((φ⁻¹).linear.det : ℝ) := by
  have hmul : ((φ⁻¹ : AffineGroup d).linear.det : ℝ) * (φ.linear.det : ℝ) = 1 := by
    rw [← affine_det_mul, inv_mul_cancel φ, affine_det_one]
  nlinarith

/-! ### The two equivalences are equivalence relations -/

theorem affinelyEquivalent_refl {d : ℕ} (G : Subgroup (EuclideanIsom d)) :
    AffinelyEquivalent G G := ⟨1, conjBy_one G⟩

theorem affinelyEquivalent_symm {d : ℕ} {G₁ G₂ : Subgroup (EuclideanIsom d)}
    (h : AffinelyEquivalent G₁ G₂) : AffinelyEquivalent G₂ G₁ := by
  obtain ⟨φ, hφ⟩ := h
  exact ⟨φ⁻¹, conjBy_inv hφ⟩

theorem affinelyEquivalent_trans {d : ℕ} {G₁ G₂ G₃ : Subgroup (EuclideanIsom d)}
    (h₁ : AffinelyEquivalent G₁ G₂) (h₂ : AffinelyEquivalent G₂ G₃) :
    AffinelyEquivalent G₁ G₃ := by
  obtain ⟨φ, hφ⟩ := h₁
  obtain ⟨ψ, hψ⟩ := h₂
  exact ⟨ψ * φ, conjBy_trans hφ hψ⟩

theorem affOPEquivalent_refl {d : ℕ} (G : Subgroup (EuclideanIsom d)) :
    AffOPEquivalent G G :=
  ⟨1, by rw [affine_det_one]; norm_num, conjBy_one G⟩

theorem affOPEquivalent_symm {d : ℕ} {G₁ G₂ : Subgroup (EuclideanIsom d)}
    (h : AffOPEquivalent G₁ G₂) : AffOPEquivalent G₂ G₁ := by
  obtain ⟨φ, hpos, hφ⟩ := h
  exact ⟨φ⁻¹, affine_det_inv_pos hpos, conjBy_inv hφ⟩

theorem affOPEquivalent_trans {d : ℕ} {G₁ G₂ G₃ : Subgroup (EuclideanIsom d)}
    (h₁ : AffOPEquivalent G₁ G₂) (h₂ : AffOPEquivalent G₂ G₃) : AffOPEquivalent G₁ G₃ := by
  obtain ⟨φ, hφpos, hφ⟩ := h₁
  obtain ⟨ψ, hψpos, hψ⟩ := h₂
  refine ⟨ψ * φ, ?_, conjBy_trans hφ hψ⟩
  rw [affine_det_mul]
  exact mul_pos hψpos hφpos

end SpaceGroupsReduction

open LeanEval.Geometry.SpaceGroupsProblem SpaceGroupsReduction

theorem solution :
    crystallographicCountOP 3 = 230 ∧
      crystallographicCount 3 = 219 ∧
        crystallographicCountOPOnly 3 = 65 := by
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨f, hex, hsep⟩ := space_groups_OP_classification
    have := encard_classes_of_reps
      (fun A B : CrystallographicGroup 3 => AffOPEquivalent A.1 B.1)
      (fun A => affOPEquivalent_refl A.1)
      (fun A B h => affOPEquivalent_symm h)
      (fun A B C h₁ h₂ => affOPEquivalent_trans h₁ h₂)
      f hex hsep
    simpa [crystallographicCountOP] using this
  · obtain ⟨f, hex, hsep⟩ := space_groups_affine_classification
    have := encard_classes_of_reps
      (fun A B : CrystallographicGroup 3 => AffinelyEquivalent A.1 B.1)
      (fun A => affinelyEquivalent_refl A.1)
      (fun A B h => affinelyEquivalent_symm h)
      (fun A B C h₁ h₂ => affinelyEquivalent_trans h₁ h₂)
      f hex hsep
    simpa [crystallographicCount] using this
  · obtain ⟨f, hex, hsep⟩ := space_groups_sohncke_classification
    have := encard_classes_of_reps
      (fun A B : { G : CrystallographicGroup 3 //
            ∀ g, g ∈ G.1 → IsOrientationPreservingIsom g } => AffOPEquivalent A.1.1 B.1.1)
      (fun A => affOPEquivalent_refl A.1.1)
      (fun A B h => affOPEquivalent_symm h)
      (fun A B C h₁ h₂ => affOPEquivalent_trans h₁ h₂)
      f hex hsep
    simpa [crystallographicCountOPOnly] using this
