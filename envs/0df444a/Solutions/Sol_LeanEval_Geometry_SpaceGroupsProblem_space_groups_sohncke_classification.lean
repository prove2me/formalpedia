-- Prove2me | solution 1 for LeanEval.Geometry.SpaceGroupsProblem.space_groups_sohncke_classification
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-09-06T08:43:15.665007+00:00
-- url     : https://prove2.me/submissions/37d7b0dd-f7f0-410e-9076-c5085b744eec
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_LeanEval_SpaceGroups_Definitions
import Theorems.Thm_LeanEval_Geometry_SpaceGroupsProblem_space_groups_master_classification

namespace SpaceGroupsSohnckeReduction

open LeanEval.Geometry.SpaceGroupsProblem

/-- `ConjBy φ G₁ G₂` says that conjugating `G₁` by the affine map `φ` produces exactly `G₂`. -/
def ConjBy {d : ℕ} (φ : AffineGroup d) (G₁ G₂ : Subgroup (EuclideanIsom d)) : Prop :=
  {h : AffineGroup d | ∃ g ∈ G₁, h = φ * g.toAffineEquiv * φ⁻¹} =
  {h : AffineGroup d | ∃ g ∈ G₂, h = g.toAffineEquiv}

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

/-! ### Determinants of linear parts -/

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

theorem affine_det_inv {d : ℕ} (φ : AffineGroup d) :
    ((φ⁻¹).linear.det : ℝ) * (φ.linear.det : ℝ) = 1 := by
  rw [← affine_det_mul, inv_mul_cancel φ, affine_det_one]

theorem affine_det_inv_pos {d : ℕ} {φ : AffineGroup d} (h : 0 < (φ.linear.det : ℝ)) :
    0 < ((φ⁻¹).linear.det : ℝ) := by
  have hmul := affine_det_inv φ
  nlinarith

/-- Affine conjugation preserves the determinant of the linear part. -/
theorem det_conj {d : ℕ} (φ g : AffineGroup d) :
    (((φ * g * φ⁻¹).linear.det : ℝ)) = (g.linear.det : ℝ) := by
  have hne : (φ.linear.det : ℝ) ≠ 0 := by
    intro h
    have := affine_det_inv φ
    rw [h, mul_zero] at this
    exact zero_ne_one this
  rw [affine_det_mul, affine_det_mul]
  have hinv : ((φ⁻¹).linear.det : ℝ) = (φ.linear.det : ℝ)⁻¹ :=
    eq_inv_of_mul_eq_one_left (affine_det_inv φ)
  rw [hinv]
  field_simp

theorem affOPEquivalent_symm {d : ℕ} {G₁ G₂ : Subgroup (EuclideanIsom d)}
    (h : AffOPEquivalent G₁ G₂) : AffOPEquivalent G₂ G₁ := by
  obtain ⟨φ, hpos, hφ⟩ := h
  exact ⟨φ⁻¹, affine_det_inv_pos hpos, conjBy_inv hφ⟩

/-- **The Sohncke property is invariant under affine equivalence.** -/
theorem sohncke_of_affinelyEquivalent {d : ℕ} {G₁ G₂ : Subgroup (EuclideanIsom d)}
    (h : AffinelyEquivalent G₁ G₂) (h₁ : ∀ g, g ∈ G₁ → IsOrientationPreservingIsom g) :
    ∀ g, g ∈ G₂ → IsOrientationPreservingIsom g := by
  obtain ⟨φ, hφ⟩ := h
  intro g hg
  have hmem : (g.toAffineEquiv) ∈ {h : AffineGroup d | ∃ g ∈ G₂, h = g.toAffineEquiv} :=
    ⟨g, hg, rfl⟩
  rw [← hφ] at hmem
  obtain ⟨g₁, hg₁, hgg⟩ := hmem
  have hdet : ((g.toAffineEquiv).linear.det : ℝ) = ((g₁.toAffineEquiv).linear.det : ℝ) := by
    rw [hgg, det_conj]
  have h₁' := h₁ g₁ hg₁
  unfold IsOrientationPreservingIsom at h₁' ⊢
  rw [hdet]
  exact h₁'

theorem sohncke_of_affOPEquivalent {d : ℕ} {G₁ G₂ : Subgroup (EuclideanIsom d)}
    (h : AffOPEquivalent G₁ G₂) (h₁ : ∀ g, g ∈ G₁ → IsOrientationPreservingIsom g) :
    ∀ g, g ∈ G₂ → IsOrientationPreservingIsom g := by
  obtain ⟨φ, _, hφ⟩ := h
  exact sohncke_of_affinelyEquivalent ⟨φ, hφ⟩ h₁

end SpaceGroupsSohnckeReduction

open LeanEval.Geometry.SpaceGroupsProblem SpaceGroupsSohnckeReduction

/-- The `65` Sohncke members of the master list form a complete irredundant list of the
Sohncke crystallographic groups up to orientation-preserving affine conjugacy. -/
theorem solution :
    ∃ f : Fin 65 →
        { G : CrystallographicGroup 3 // ∀ g, g ∈ G.1 → IsOrientationPreservingIsom g },
      (∀ G : { G : CrystallographicGroup 3 // ∀ g, g ∈ G.1 → IsOrientationPreservingIsom g },
          ∃ i : Fin 65, AffOPEquivalent (f i).1.1 G.1.1) ∧
        (∀ i j : Fin 65, AffOPEquivalent (f i).1.1 (f j).1.1 → i = j) := by
  obtain ⟨f, hex, hsep, -, ⟨t, htinj, ht⟩⟩ := space_groups_master_classification
  refine ⟨fun k => ⟨f (t k), (ht (t k)).2 ⟨k, rfl⟩⟩, ?_, ?_⟩
  · rintro ⟨G, hG⟩
    obtain ⟨i, hi⟩ := hex G
    have hfi : ∀ g, g ∈ (f i).1 → IsOrientationPreservingIsom g :=
      sohncke_of_affOPEquivalent (affOPEquivalent_symm hi) hG
    obtain ⟨k, hk⟩ := (ht i).1 hfi
    refine ⟨k, ?_⟩
    simpa [hk] using hi
  · intro i j hij
    exact htinj (hsep _ _ hij)
