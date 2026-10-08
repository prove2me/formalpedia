-- Prove2me | solution 1 for GeometryOfGraphs.EuclidDist.gram_reformulation
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-06T21:06:59.422832+00:00
-- url     : https://prove2.me/submissions/8cec42e7-5588-42c4-9f3e-f17b57e67595

import Mathlib
import Definitions.Def_GeometryOfGraphs_EuclidDist_EuclideanDistortion
open GeometryOfGraphs.EuclidDist
open Matrix
open scoped MatrixOrder

private lemma sqdist {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (u v : E) : ‖u-v‖^2 = inner ℝ u u + inner ℝ v v - 2*inner ℝ u v := by
  rw [norm_sub_sq_real, real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq]
  ring

private lemma realization {X : Type*} [Fintype X] [DecidableEq X]
    (A : Matrix X X ℝ) (hA : A.PosSemidef) :
    ∃ ψ : X → EuclideanSpace ℝ (Fin (Fintype.card X)),
      ∀ i j, inner ℝ (ψ i) (ψ j) = A i j := by
  let B := CFC.sqrt A
  have hB : star B = B := (CFC.sqrt_nonneg A).isSelfAdjoint.star_eq
  have hBB : Bᴴ * B = A := by
    rw [← Matrix.star_eq_conjTranspose, hB]
    exact CFC.sqrt_mul_sqrt_self A hA.nonneg
  let v : X → EuclideanSpace ℝ X := fun i => WithLp.toLp 2 (fun k => B k i)
  have hv (i j : X) : inner ℝ (v i) (v j) = A i j := by
    rw [← hBB]
    simp [v, PiLp.inner_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, real_inner_comm,
      RCLike.inner_apply, mul_comm]
  let e := LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (Fintype.equivFin X)
  exact ⟨fun i => e (v i), fun i j => by rw [e.inner_map_map]; exact hv i j⟩

theorem solution {X : Type*} [Fintype X] [DecidableEq X]
    (d : X → X → ℝ) (hd : GeometryOfGraphs.FlowCut.IsPseudometric d) (c : ℝ) (hc : 1 ≤ c) :
    EmbedsEuclidean d c ↔
      ∃ A : Matrix X X ℝ, A.PosSemidef ∧
        ∀ i j, d i j ^ 2 ≤ A i i + A j j - 2 * A i j ∧
          A i i + A j j - 2 * A i j ≤ c ^ 2 * d i j ^ 2 := by
  have hc0 : 0 < c := by linarith
  constructor
  · rintro ⟨m, φ, hφ⟩
    let ψ := fun i => c • φ i
    refine ⟨Matrix.gram ℝ ψ, Matrix.posSemidef_gram ℝ ψ, ?_⟩
    intro i j
    have hn : ‖ψ i-ψ j‖ = c*‖φ i-φ j‖ := by
      dsimp [ψ]
      rw [← smul_sub, norm_smul, Real.norm_of_nonneg hc0.le]
    have hs : (Matrix.gram ℝ ψ) i i + (Matrix.gram ℝ ψ) j j - 2*(Matrix.gram ℝ ψ) i j =
        c^2*‖φ i-φ j‖^2 := by
      rw [Matrix.gram_apply, Matrix.gram_apply, Matrix.gram_apply, ← sqdist, hn, mul_pow]
    rw [hs]
    obtain ⟨h1,h2⟩ := hφ i j
    have hd0 := hd.2.1 i j
    constructor
    · nlinarith [sq_nonneg (c*‖φ i-φ j‖-d i j)]
    · exact mul_le_mul_of_nonneg_left (sq_le_sq₀ (norm_nonneg _) hd0 |>.mpr h1) (sq_nonneg c)
  · rintro ⟨A,hA,h⟩
    obtain ⟨ψ,hψ⟩ := realization A hA
    refine ⟨Fintype.card X, fun i => (1/c) • ψ i, ?_⟩
    intro i j
    have hs : ‖ψ i-ψ j‖^2 = A i i + A j j - 2*A i j := by rw [sqdist, hψ, hψ, hψ]
    have hn : ‖(1/c) • ψ i-(1/c) • ψ j‖ = ‖ψ i-ψ j‖/c := by
      rw [← smul_sub, norm_smul, Real.norm_of_nonneg (by positivity : 0 ≤ (1:ℝ)/c)]
      ring
    rw [hn]
    have hd0 := hd.2.1 i j
    have hh := h i j
    rw [← hs] at hh
    have h1 : ‖ψ i-ψ j‖ ≤ c*d i j := by
      apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hc0.le hd0)).mp
      simpa [mul_pow] using hh.2
    have h2 : d i j ≤ ‖ψ i-ψ j‖ := (sq_le_sq₀ hd0 (norm_nonneg _)).mp hh.1
    constructor
    · exact (div_le_iff₀ hc0).mpr (by simpa [mul_comm] using h1)
    · simpa [mul_div_cancel₀ _ hc0.ne'] using h2

#print axioms solution
