-- Prove2me | solution 1 for LeanEval.Geometry.SpaceGroupsProblem.space_groups_affine_classification
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-09-06T08:43:14.617482+00:00
-- url     : https://prove2.me/submissions/bed5f4d1-dd28-4217-8f9e-9bff20748569
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_LeanEval_SpaceGroups_Definitions
import Theorems.Thm_LeanEval_Geometry_SpaceGroupsProblem_space_groups_master_classification

namespace SpaceGroupsAffineReduction

open LeanEval.Geometry.SpaceGroupsProblem

/-- `ConjBy φ G₁ G₂` says that conjugating `G₁` by the affine map `φ` produces exactly `G₂`. -/
def ConjBy {d : ℕ} (φ : AffineGroup d) (G₁ G₂ : Subgroup (EuclideanIsom d)) : Prop :=
  {h : AffineGroup d | ∃ g ∈ G₁, h = φ * g.toAffineEquiv * φ⁻¹} =
  {h : AffineGroup d | ∃ g ∈ G₂, h = g.toAffineEquiv}

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

theorem affinelyEquivalent_trans {d : ℕ} {G₁ G₂ G₃ : Subgroup (EuclideanIsom d)}
    (h₁ : AffinelyEquivalent G₁ G₂) (h₂ : AffinelyEquivalent G₂ G₃) :
    AffinelyEquivalent G₁ G₃ := by
  obtain ⟨φ, hφ⟩ := h₁
  obtain ⟨ψ, hψ⟩ := h₂
  exact ⟨ψ * φ, conjBy_trans hφ hψ⟩

/-- Orientation-preserving affine equivalence refines affine equivalence. -/
theorem affinelyEquivalent_of_affOPEquivalent {d : ℕ} {G₁ G₂ : Subgroup (EuclideanIsom d)}
    (h : AffOPEquivalent G₁ G₂) : AffinelyEquivalent G₁ G₂ := by
  obtain ⟨φ, _, hφ⟩ := h
  exact ⟨φ, hφ⟩

end SpaceGroupsAffineReduction

open LeanEval.Geometry.SpaceGroupsProblem SpaceGroupsAffineReduction

/-- The `219` members selected by the master enumeration form a complete irredundant list
for arbitrary affine conjugacy. -/
theorem solution :
    ∃ f : Fin 219 → CrystallographicGroup 3,
      (∀ G : CrystallographicGroup 3, ∃ i : Fin 219, AffinelyEquivalent (f i).1 G.1) ∧
        (∀ i j : Fin 219, AffinelyEquivalent (f i).1 (f j).1 → i = j) := by
  obtain ⟨f, hex, -, ⟨s, hsex, hssep⟩, -⟩ := space_groups_master_classification
  refine ⟨fun k => f (s k), ?_, hssep⟩
  intro G
  obtain ⟨i, hi⟩ := hex G
  obtain ⟨k, hk⟩ := hsex i
  exact ⟨k, affinelyEquivalent_trans hk (affinelyEquivalent_of_affOPEquivalent hi)⟩
