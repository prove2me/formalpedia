-- Prove2me | solution 1 for NearEnemy.sharedBisector_parallel_and_sum_orth
-- status  : ACCEPTED   (prove)
-- author  : @mysticflounder
-- created : 2026-09-18T14:56:38.578838+00:00
-- url     : https://prove2.me/submissions/212934cb-bb3a-41c7-8e65-19f70785c719

import Mathlib
import Definitions.Def_NearEnemyDefs

universe u_1
open scoped RealInnerProductSpace
open scoped Classical
open MvPolynomial
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable {ι : Type*} [Fintype ι]
open NearEnemy
namespace NearEnemy

/-- The module-local `perpBisector` is the coercion of mathlib's
affine-subspace perpendicular bisector. -/
theorem perpBisector_eq_coe (p q : EuclideanSpace ℝ (Fin 2)) :
    perpBisector p q = ↑(AffineSubspace.perpBisector p q) := by
  ext x
  simp [perpBisector, AffineSubspace.mem_perpBisector_iff_dist_eq]

end NearEnemy

open NearEnemy in
theorem solution {p q p' q' : EuclideanSpace ℝ (Fin 2)}
    (h : perpBisector p q = perpBisector p' q') :
    (∃ t : ℝ, q' - p' = t • (q - p)) ∧ ⟪p + q - (p' + q'), q - p⟫ = 0 := by
  -- Promote the set equality to mathlib's affine-subspace bisector.
  have hS : AffineSubspace.perpBisector p q =
      AffineSubspace.perpBisector p' q' :=
    AffineSubspace.coe_injective
      (by rw [← perpBisector_eq_coe, ← perpBisector_eq_coe, h])
  constructor
  · -- (1) Equal affine subspaces have equal directions; the directions are
    -- the orthogonal complements of the difference-vector spans, and the
    -- double orthogonal complement recovers the spans.
    have hdir := congrArg AffineSubspace.direction hS
    rw [AffineSubspace.direction_perpBisector,
      AffineSubspace.direction_perpBisector] at hdir
    have hspan : (ℝ ∙ (q -ᵥ p)) = (ℝ ∙ (q' -ᵥ p')) := by
      have horth := congrArg Submodule.orthogonal hdir
      rwa [Submodule.orthogonal_orthogonal, Submodule.orthogonal_orthogonal]
        at horth
    have hmem : q' - p' ∈ (ℝ ∙ (q - p)) := by
      have hself : q' -ᵥ p' ∈ (ℝ ∙ (q' -ᵥ p')) :=
        Submodule.mem_span_singleton_self _
      rw [← hspan] at hself
      simpa [vsub_eq_sub] using hself
    obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.mp hmem
    exact ⟨t, ht.symm⟩
  · -- (2) Both midpoints lie on the common bisector, so their difference is
    -- in its direction, i.e. orthogonal to the normal `q - p`.
    have hm : midpoint ℝ p q ∈ AffineSubspace.perpBisector p q :=
      AffineSubspace.midpoint_mem_perpBisector p q
    have hm' : midpoint ℝ p' q' ∈ AffineSubspace.perpBisector p q := by
      rw [hS]
      exact AffineSubspace.midpoint_mem_perpBisector p' q'
    have hd := AffineSubspace.vsub_mem_direction hm hm'
    rw [AffineSubspace.direction_perpBisector] at hd
    have hinner : ⟪q - p, midpoint ℝ p q - midpoint ℝ p' q'⟫ = 0 := by
      have := Submodule.mem_orthogonal_singleton_iff_inner_right.mp hd
      simpa [vsub_eq_sub] using this
    have h2m : (2 : ℝ) • (midpoint ℝ p q - midpoint ℝ p' q') =
        p + q - (p' + q') := by
      rw [smul_sub, two_smul, two_smul, midpoint_add_self, midpoint_add_self]
    calc ⟪p + q - (p' + q'), q - p⟫
        = ⟪(2 : ℝ) • (midpoint ℝ p q - midpoint ℝ p' q'), q - p⟫ := by
          rw [h2m]
      _ = 2 * ⟪midpoint ℝ p q - midpoint ℝ p' q', q - p⟫ :=
          real_inner_smul_left _ _ _
      _ = 2 * ⟪q - p, midpoint ℝ p q - midpoint ℝ p' q'⟫ := by
          rw [real_inner_comm]
      _ = 0 := by rw [hinner, mul_zero]
