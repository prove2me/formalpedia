-- Prove2me | solution 2 for LeanEval.Geometry.SpaceGroupsProblem.space_groups
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @t4v1
-- created : 2026-09-10T06:24:39.237227+00:00
-- url     : https://prove2.me/submissions/1be787f6-2bcb-4828-97c2-6ab8f754ff45
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_LeanEval_Geometry_SpaceGroupsProblem_space_groups_OP_classification
import Theorems.Thm_LeanEval_Geometry_SpaceGroupsProblem_space_groups_affine_classification
import Theorems.Thm_LeanEval_Geometry_SpaceGroupsProblem_space_groups_sohncke_classification

/-!
Reduction of the three space-group counts to the three classification theorems.

Each count is the cardinality of the set of equivalence classes.  A classification
theorem supplies a complete, irredundant list of representatives.  Passing from the
latter to the former needs two ingredients that the classification theorems do not
themselves state: that the equivalence used is genuinely an equivalence relation,
and that a complete irredundant list enumerates the classes injectively.
-/

namespace SpaceGroupsReduction

open LeanEval Geometry SpaceGroupsProblem

variable {d : ℕ}

/-- The image of a subgroup of the isometry group inside the affine group. -/
private def img (G : Subgroup (EuclideanIsom d)) : Set (AffineGroup d) :=
  {h : AffineGroup d | ∃ g ∈ G, h = g.toAffineEquiv}

/-- The set appearing in the equivalence definitions is the conjugate of `img`. -/
private lemma conj_set (φ : AffineGroup d) (G : Subgroup (EuclideanIsom d)) :
    {h : AffineGroup d | ∃ g ∈ G, h = φ * g.toAffineEquiv * φ⁻¹}
      = (fun h => φ * h * φ⁻¹) '' img G := by
  ext h
  simp only [Set.mem_image, Set.mem_setOf_eq, img]
  constructor
  · rintro ⟨g, hg, rfl⟩; exact ⟨g.toAffineEquiv, ⟨g, hg, rfl⟩, rfl⟩
  · rintro ⟨x, ⟨g, hg, rfl⟩, rfl⟩; exact ⟨g, hg, rfl⟩

private lemma conj_conj (φ : AffineGroup d) (A : Set (AffineGroup d)) :
    (fun h => φ⁻¹ * h * (φ⁻¹)⁻¹) '' ((fun h => φ * h * φ⁻¹) '' A) = A := by
  rw [Set.image_image]
  have h : (fun h : AffineGroup d => φ⁻¹ * (φ * h * φ⁻¹) * (φ⁻¹)⁻¹) = id := by
    funext h; simp [mul_assoc]
  rw [h, Set.image_id]

private lemma conj_comp (φ ψ : AffineGroup d) (A : Set (AffineGroup d)) :
    (fun h => φ * h * φ⁻¹) '' ((fun h => ψ * h * ψ⁻¹) '' A)
      = (fun h => (φ * ψ) * h * (φ * ψ)⁻¹) '' A := by
  rw [Set.image_image]
  have h : (fun h : AffineGroup d => φ * (ψ * h * ψ⁻¹) * φ⁻¹)
      = (fun h : AffineGroup d => (φ * ψ) * h * (φ * ψ)⁻¹) := by
    funext x; simp [mul_assoc, mul_inv_rev]
  rw [h]

/-- `AffinelyEquivalent`, restated as conjugation of images. -/
private lemma affEq_iff (G₁ G₂ : Subgroup (EuclideanIsom d)) :
    AffinelyEquivalent G₁ G₂ ↔
      ∃ φ : AffineGroup d, (fun h => φ * h * φ⁻¹) '' img G₁ = img G₂ := by
  unfold AffinelyEquivalent
  constructor
  · rintro ⟨φ, hφ⟩; exact ⟨φ, by rw [← conj_set]; exact hφ⟩
  · rintro ⟨φ, hφ⟩; exact ⟨φ, by rw [conj_set]; exact hφ⟩

private lemma affOPEq_iff (G₁ G₂ : Subgroup (EuclideanIsom d)) :
    AffOPEquivalent G₁ G₂ ↔
      ∃ φ : AffineGroup d, 0 < (φ.linear.det : ℝ) ∧
        (fun h => φ * h * φ⁻¹) '' img G₁ = img G₂ := by
  unfold AffOPEquivalent
  constructor
  · rintro ⟨φ, hd, hφ⟩; exact ⟨φ, hd, by rw [← conj_set]; exact hφ⟩
  · rintro ⟨φ, hd, hφ⟩; exact ⟨φ, hd, by rw [conj_set]; exact hφ⟩

-- determinants

private lemma det_mul (a b : AffineGroup d) :
    (((a * b).linear).det : ℝ) = ((a.linear).det : ℝ) * ((b.linear).det : ℝ) := by
  have h : (a * b).linear = a.linear * b.linear := rfl
  rw [h]
  simp

private lemma det_one : (((1 : AffineGroup d).linear).det : ℝ) = 1 := by
  have h : ((1 : AffineGroup d).linear) = 1 := rfl
  rw [h]
  simp

private lemma det_inv_pos {φ : AffineGroup d} (h : 0 < (φ.linear.det : ℝ)) :
    0 < (((φ⁻¹ : AffineGroup d).linear).det : ℝ) := by
  have h1 : (((φ⁻¹ : AffineGroup d).linear).det : ℝ) * ((φ.linear).det : ℝ) = 1 := by
    rw [← det_mul, inv_mul_cancel, det_one]
  by_contra hc
  push_neg at hc
  nlinarith

-- equivalence properties

private lemma affEq_refl (G : Subgroup (EuclideanIsom d)) : AffinelyEquivalent G G := by
  rw [affEq_iff]
  exact ⟨1, by simp⟩

private lemma affEq_symm {G₁ G₂ : Subgroup (EuclideanIsom d)}
    (h : AffinelyEquivalent G₁ G₂) : AffinelyEquivalent G₂ G₁ := by
  rw [affEq_iff] at h ⊢
  obtain ⟨φ, hφ⟩ := h
  exact ⟨φ⁻¹, by rw [← hφ, conj_conj]⟩

private lemma affEq_trans {G₁ G₂ G₃ : Subgroup (EuclideanIsom d)}
    (h₁ : AffinelyEquivalent G₁ G₂) (h₂ : AffinelyEquivalent G₂ G₃) :
    AffinelyEquivalent G₁ G₃ := by
  rw [affEq_iff] at h₁ h₂ ⊢
  obtain ⟨φ, hφ⟩ := h₁
  obtain ⟨ψ, hψ⟩ := h₂
  exact ⟨ψ * φ, by rw [← conj_comp, hφ, hψ]⟩

private lemma affOP_refl (G : Subgroup (EuclideanIsom d)) : AffOPEquivalent G G := by
  rw [affOPEq_iff]
  exact ⟨1, by rw [det_one]; norm_num, by simp⟩

private lemma affOP_symm {G₁ G₂ : Subgroup (EuclideanIsom d)}
    (h : AffOPEquivalent G₁ G₂) : AffOPEquivalent G₂ G₁ := by
  rw [affOPEq_iff] at h ⊢
  obtain ⟨φ, hd, hφ⟩ := h
  exact ⟨φ⁻¹, det_inv_pos hd, by rw [← hφ, conj_conj]⟩

private lemma affOP_trans {G₁ G₂ G₃ : Subgroup (EuclideanIsom d)}
    (h₁ : AffOPEquivalent G₁ G₂) (h₂ : AffOPEquivalent G₂ G₃) :
    AffOPEquivalent G₁ G₃ := by
  rw [affOPEq_iff] at h₁ h₂ ⊢
  obtain ⟨φ, hdφ, hφ⟩ := h₁
  obtain ⟨ψ, hdψ, hψ⟩ := h₂
  refine ⟨ψ * φ, ?_, by rw [← conj_comp, hφ, hψ]⟩
  rw [det_mul]
  positivity

/-- A complete, irredundant list of representatives enumerates the classes. -/
private lemma encard_classes {X : Type*} {N : ℕ} {R : X → X → Prop}
    (hrefl : ∀ x, R x x)
    (hsymm : ∀ {x y}, R x y → R y x)
    (htrans : ∀ {x y z}, R x y → R y z → R x z)
    (f : Fin N → X)
    (hcomplete : ∀ x, ∃ i, R (f i) x)
    (hirred : ∀ i j, R (f i) (f j) → i = j) :
    Set.encard {S : Set X | ∃ x : X, S = {y | R x y}} = N := by
  have hset : {S : Set X | ∃ x : X, S = {y | R x y}}
      = Set.range (fun i : Fin N => {y | R (f i) y}) := by
    ext S
    constructor
    · rintro ⟨x, rfl⟩
      obtain ⟨i, hi⟩ := hcomplete x
      refine ⟨i, ?_⟩
      ext y
      show R (f i) y ↔ R x y
      exact ⟨fun hy => htrans (hsymm hi) hy, fun hy => htrans hi hy⟩
    · rintro ⟨i, rfl⟩
      exact ⟨f i, rfl⟩
  have hinj : Function.Injective (fun i : Fin N => {y | R (f i) y}) := by
    intro i j hij
    refine hirred i j ?_
    have heq : {y | R (f i) y} = {y | R (f j) y} := hij
    have hmem : f j ∈ {y | R (f j) y} := hrefl (f j)
    rw [← heq] at hmem
    exact hmem
  rw [hset, ← Set.image_univ, hinj.encard_image, Set.encard_univ]
  simp

end SpaceGroupsReduction

open LeanEval Geometry SpaceGroupsProblem SpaceGroupsReduction in
theorem solution :
    crystallographicCountOP 3 = 230 ∧
      crystallographicCount 3 = 219 ∧
        crystallographicCountOPOnly 3 = 65 := by
  obtain ⟨f₁, hc₁, hi₁⟩ := space_groups_OP_classification
  obtain ⟨f₂, hc₂, hi₂⟩ := space_groups_affine_classification
  obtain ⟨f₃, hc₃, hi₃⟩ := space_groups_sohncke_classification
  refine ⟨?_, ?_, ?_⟩
  · have := encard_classes (X := CrystallographicGroup 3)
      (R := fun a b => AffOPEquivalent a.1 b.1)
      (fun x => affOP_refl x.1) (fun h => affOP_symm h) (fun h₁ h₂ => affOP_trans h₁ h₂)
      f₁ hc₁ hi₁
    simpa [crystallographicCountOP] using this
  · have := encard_classes (X := CrystallographicGroup 3)
      (R := fun a b => AffinelyEquivalent a.1 b.1)
      (fun x => affEq_refl x.1) (fun h => affEq_symm h) (fun h₁ h₂ => affEq_trans h₁ h₂)
      f₂ hc₂ hi₂
    simpa [crystallographicCount] using this
  · have := encard_classes
      (X := { G : CrystallographicGroup 3 // ∀ g, g ∈ G.1 → IsOrientationPreservingIsom g })
      (R := fun a b => AffOPEquivalent a.1.1 b.1.1)
      (fun x => affOP_refl x.1.1) (fun h => affOP_symm h) (fun h₁ h₂ => affOP_trans h₁ h₂)
      f₃ hc₃ hi₃
    simpa [crystallographicCountOPOnly] using this
