-- Prove2me | solution 1 for LeanEval.Geometry.SpaceGroupsProblem.pointGroup_integral_matrix
-- status  : ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-09-06T07:38:26.740845+00:00
-- url     : https://prove2.me/submissions/cd273a53-eb18-49d3-814b-eb33d7fc1b7f

import Mathlib
import Definitions.Def_LeanEval_SpaceGroups_Definitions
import Definitions.Def_SpaceGroupsPointGroupDefs
import Theorems.Thm_LeanEval_Geometry_SpaceGroupsProblem_transLattice_eq_span_of_real_basis

open LeanEval.Geometry.SpaceGroupsProblem

namespace SpaceGroupsIntegralRep

variable {d : ℕ}

/-- The point group acts on the translation vectors. -/
theorem linPart_mem_transVectors {G : Subgroup (EuclideanIsom d)} {g : EuclideanIsom d}
    (hg : g ∈ G) {v : E d} (hv : v ∈ transVectors G) : linPart g v ∈ transVectors G := by
  obtain ⟨t, htG, ht⟩ := hv
  refine ⟨g * t * g⁻¹, G.mul_mem (G.mul_mem hg htG) (G.inv_mem hg), ?_⟩
  intro x
  have h1 : (g * t * g⁻¹) x = g (t (g⁻¹ x)) := rfl
  rw [h1, ht (g⁻¹ x)]
  have h2 : linPart g v = g (g⁻¹ x + v) - g (g⁻¹ x) := linPart_apply_add g (g⁻¹ x) v
  have h3 : g (g⁻¹ x) = x := by
    have hgg : (g * g⁻¹) x = x := by simp
    simpa using hgg
  rw [h3] at h2
  rw [h2]
  abel

/-- The point group preserves the translation lattice. -/
theorem pointGroup_mapsTo {G : Subgroup (EuclideanIsom d)} {A : E d ≃ₗᵢ[ℝ] E d}
    (hA : A ∈ pointGroup G) {v : E d} (hv : v ∈ transSubmoduleZ G) :
    A v ∈ transSubmoduleZ G := by
  obtain ⟨g, hg, rfl⟩ := hA
  exact linPart_mem_transVectors hg hv

end SpaceGroupsIntegralRep

open SpaceGroupsIntegralRep

theorem solution {d : ℕ} {G : Subgroup (EuclideanIsom d)} (hG : IsCrystallographicGroup G) :
    ∃ w : Fin d → E d, LinearIndependent ℝ w ∧
      Submodule.span ℤ (Set.range w) = transSubmoduleZ G ∧
      ∀ A ∈ pointGroup G, ∃ M : Matrix (Fin d) (Fin d) ℤ,
        ∀ j, A (w j) = ∑ i, (M i j : ℝ) • w i := by
  obtain ⟨w, hwli, hwspan⟩ := transLattice_eq_span_of_real_basis hG
  refine ⟨w, hwli, hwspan, ?_⟩
  intro A hA
  have hw : ∀ j, w j ∈ transSubmoduleZ G := by
    intro j
    rw [← hwspan]
    exact Submodule.subset_span ⟨j, rfl⟩
  have hmem : ∀ j, A (w j) ∈ Submodule.span ℤ (Set.range w) := by
    intro j
    rw [hwspan]
    exact pointGroup_mapsTo hA (hw j)
  choose c hc using fun j => (Submodule.mem_span_range_iff_exists_fun ℤ).1 (hmem j)
  refine ⟨Matrix.of fun i j => c j i, fun j => ?_⟩
  rw [← hc j]
  simp [Int.cast_smul_eq_zsmul]
