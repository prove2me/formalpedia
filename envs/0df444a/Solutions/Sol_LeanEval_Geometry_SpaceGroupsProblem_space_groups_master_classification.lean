-- Prove2me | solution 1 for LeanEval.Geometry.SpaceGroupsProblem.space_groups_master_classification
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-09-27T11:06:40.242193+00:00
-- url     : https://prove2.me/submissions/f1312bd4-15ea-4bea-9a0e-bd1eb2b50432
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_LeanEval_SpaceGroups_Definitions
import Definitions.Def_SpaceGroupCatalog
import Theorems.Thm_LeanEval_Geometry_SpaceGroupsProblem_SpaceGroupCatalog_spaceGroupCatalog_isCrystallographic
import Theorems.Thm_LeanEval_Geometry_SpaceGroupsProblem_SpaceGroupCatalog_spaceGroupCatalog_complete
import Theorems.Thm_LeanEval_Geometry_SpaceGroupsProblem_SpaceGroupCatalog_spaceGroupCatalog_affine_cover
import Theorems.Thm_LeanEval_Geometry_SpaceGroupsProblem_SpaceGroupCatalog_spaceGroupCatalog_affine_irredundant
import Theorems.Thm_LeanEval_Geometry_SpaceGroupsProblem_SpaceGroupCatalog_spaceGroupCatalog_enantiomorphs_chiral
import Theorems.Thm_LeanEval_Geometry_SpaceGroupsProblem_SpaceGroupCatalog_spaceGroupCatalog_sohncke

/-!
Reduction of the master enumeration of the 230 space groups to properties of the explicit
catalogue `spaceGroupCatalog`.
-/

namespace SpaceGroupMasterReduction

open LeanEval Geometry SpaceGroupsProblem SpaceGroupCatalog

variable {d : ℕ}

lemma affOP_affEq {G₁ G₂ : Subgroup (EuclideanIsom d)} (h : AffOPEquivalent G₁ G₂) :
    AffinelyEquivalent G₁ G₂ := by
  obtain ⟨φ, -, hφ⟩ := h
  exact ⟨φ, hφ⟩

lemma conj_mem_iff {G₁ G₂ : Subgroup (EuclideanIsom d)} {φ : AffineGroup d}
    (hφ : {h : AffineGroup d | ∃ g ∈ G₁, h = φ * g.toAffineEquiv * φ⁻¹} =
      {h : AffineGroup d | ∃ g ∈ G₂, h = g.toAffineEquiv}) (h : AffineGroup d) :
    (∃ g ∈ G₁, h = φ * g.toAffineEquiv * φ⁻¹) ↔ ∃ g ∈ G₂, h = g.toAffineEquiv := by
  have := congrArg (fun S => h ∈ S) hφ
  simpa using this

lemma symm_set {G₁ G₂ : Subgroup (EuclideanIsom d)} {φ : AffineGroup d}
    (hφ : {h : AffineGroup d | ∃ g ∈ G₁, h = φ * g.toAffineEquiv * φ⁻¹} =
      {h : AffineGroup d | ∃ g ∈ G₂, h = g.toAffineEquiv}) :
    {h : AffineGroup d | ∃ g ∈ G₂, h = φ⁻¹ * g.toAffineEquiv * φ⁻¹⁻¹} =
      {h : AffineGroup d | ∃ g ∈ G₁, h = g.toAffineEquiv} := by
  ext h
  simp only [Set.mem_ofPred_eq]
  constructor
  · rintro ⟨g₂, hg₂, rfl⟩
    obtain ⟨g₁, hg₁, he⟩ := (conj_mem_iff hφ g₂.toAffineEquiv).2 ⟨g₂, hg₂, rfl⟩
    refine ⟨g₁, hg₁, ?_⟩
    rw [he]
    group
  · rintro ⟨g₁, hg₁, rfl⟩
    obtain ⟨g₂, hg₂, he⟩ :=
      (conj_mem_iff hφ (φ * g₁.toAffineEquiv * φ⁻¹)).1 ⟨g₁, hg₁, rfl⟩
    refine ⟨g₂, hg₂, ?_⟩
    rw [← he]
    group

lemma affEq_symm {G₁ G₂ : Subgroup (EuclideanIsom d)} (h : AffinelyEquivalent G₁ G₂) :
    AffinelyEquivalent G₂ G₁ := by
  obtain ⟨φ, hφ⟩ := h
  exact ⟨φ⁻¹, symm_set hφ⟩

lemma det_inv_pos {φ : AffineGroup d} (h : 0 < (φ.linear.det : ℝ)) :
    0 < ((φ⁻¹).linear.det : ℝ) := by
  have h1 : ((φ⁻¹).linear.det : ℝ) * (φ.linear.det : ℝ) = 1 := by
    rw [← Units.val_mul, ← map_mul]
    have : (φ⁻¹).linear * φ.linear = 1 := by
      ext x : 1
      exact congrArg (fun ψ : AffineGroup d => ψ.linear x) (inv_mul_cancel φ)
    rw [this, map_one, Units.val_one]
  by_contra hc
  push Not at hc
  nlinarith

lemma affOP_symm {G₁ G₂ : Subgroup (EuclideanIsom d)} (h : AffOPEquivalent G₁ G₂) :
    AffOPEquivalent G₂ G₁ := by
  obtain ⟨φ, hd, hφ⟩ := h
  exact ⟨φ⁻¹, det_inv_pos hd, symm_set hφ⟩

lemma affEq_trans {G₁ G₂ G₃ : Subgroup (EuclideanIsom d)} (h₁ : AffinelyEquivalent G₁ G₂)
    (h₂ : AffinelyEquivalent G₂ G₃) : AffinelyEquivalent G₁ G₃ := by
  obtain ⟨φ, hφ⟩ := h₁
  obtain ⟨ψ, hψ⟩ := h₂
  refine ⟨ψ * φ, ?_⟩
  ext h
  simp only [Set.mem_ofPred_eq]
  constructor
  · rintro ⟨g₁, hg₁, rfl⟩
    obtain ⟨g₂, hg₂, he⟩ := (conj_mem_iff hφ (φ * g₁.toAffineEquiv * φ⁻¹)).1 ⟨g₁, hg₁, rfl⟩
    obtain ⟨g₃, hg₃, he'⟩ :=
      (conj_mem_iff hψ (ψ * g₂.toAffineEquiv * ψ⁻¹)).1 ⟨g₂, hg₂, rfl⟩
    refine ⟨g₃, hg₃, ?_⟩
    rw [← he', ← he]
    group
  · rintro ⟨g₃, hg₃, rfl⟩
    obtain ⟨g₂, hg₂, he⟩ := (conj_mem_iff hψ g₃.toAffineEquiv).2 ⟨g₃, hg₃, rfl⟩
    obtain ⟨g₁, hg₁, he'⟩ := (conj_mem_iff hφ g₂.toAffineEquiv).2 ⟨g₂, hg₂, rfl⟩
    refine ⟨g₁, hg₁, ?_⟩
    rw [he, he']
    group

set_option maxRecDepth 100000 in
lemma class_cases :
    ∀ i : Fin 230, affineRepIndex (affineClassIndex i) = i ∨
      (affineRepIndex (affineClassIndex i), i) ∈ enantiomorphicPairs := by
  decide +kernel

lemma pairs_functional (a b c : Fin 230) (h1 : (a, b) ∈ enantiomorphicPairs)
    (h2 : (a, c) ∈ enantiomorphicPairs) : b = c := by
  simp only [enantiomorphicPairs, List.mem_cons, List.not_mem_nil, or_false,
    Prod.mk.injEq] at h1 h2
  omega

lemma op_irredundant (i j : Fin 230)
    (hij : AffOPEquivalent (spaceGroupCatalog i) (spaceGroupCatalog j)) : i = j := by
  have hc : affineClassIndex i = affineClassIndex j :=
    spaceGroupCatalog_affine_irredundant (affineClassIndex i) (affineClassIndex j)
      (affEq_trans (affEq_trans (spaceGroupCatalog_affine_cover i) (affOP_affEq hij))
        (affEq_symm (spaceGroupCatalog_affine_cover j)))
  have hr : affineRepIndex (affineClassIndex i) = affineRepIndex (affineClassIndex j) := by
    rw [hc]
  rcases class_cases i with hi | hi <;> rcases class_cases j with hj | hj
  · rw [← hi, ← hj, hr]
  · rw [← hr, hi] at hj
    have h := spaceGroupCatalog_enantiomorphs_chiral (i, j) hj
    dsimp only at h
    exact absurd hij h
  · rw [hr, hj] at hi
    have h := spaceGroupCatalog_enantiomorphs_chiral (j, i) hi
    dsimp only at h
    exact absurd (affOP_symm hij) h
  · rw [hr] at hi
    exact pairs_functional _ i j hi hj

end SpaceGroupMasterReduction

open LeanEval Geometry SpaceGroupsProblem SpaceGroupCatalog SpaceGroupMasterReduction in
theorem solution :
    ∃ f : Fin 230 → CrystallographicGroup 3,
      (∀ G : CrystallographicGroup 3, ∃ i : Fin 230, AffOPEquivalent (f i).1 G.1) ∧
      (∀ i j : Fin 230, AffOPEquivalent (f i).1 (f j).1 → i = j) ∧
      (∃ s : Fin 219 → Fin 230,
        (∀ i : Fin 230, ∃ k : Fin 219, AffinelyEquivalent (f (s k)).1 (f i).1) ∧
        (∀ k l : Fin 219, AffinelyEquivalent (f (s k)).1 (f (s l)).1 → k = l)) ∧
      (∃ t : Fin 65 → Fin 230, Function.Injective t ∧
        ∀ i : Fin 230,
          (∀ g, g ∈ (f i).1 → IsOrientationPreservingIsom g) ↔ ∃ k : Fin 65, t k = i) :=
  ⟨fun i => ⟨spaceGroupCatalog i, spaceGroupCatalog_isCrystallographic i⟩,
    spaceGroupCatalog_complete, op_irredundant,
    ⟨affineRepIndex, fun i => ⟨affineClassIndex i, spaceGroupCatalog_affine_cover i⟩,
      spaceGroupCatalog_affine_irredundant⟩,
    ⟨sohnckeIndex, spaceGroupCatalog_sohncke⟩⟩
