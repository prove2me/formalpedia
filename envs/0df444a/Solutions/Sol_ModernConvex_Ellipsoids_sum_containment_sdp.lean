-- Prove2me | solution 1 for ModernConvex.Ellipsoids.sum_containment_sdp
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T12:35:22.774577+00:00
-- url     : https://prove2.me/submissions/218f8a00-a662-4aa9-bde8-c8c39bfe226b

import Mathlib
import Definitions.Def_ModernConvex_Ellipsoids_Ellipsoid
import Definitions.Def_ModernConvex_Ellipsoids_Programs

open Matrix
open ModernConvex.Ellipsoids
theorem g69a2_blockSel_quad {m n : ℕ} (B : Fin m → Matrix (Fin n) (Fin n) ℝ) (i : Fin m)
    (w : Fin m × Fin n → ℝ) :
    w ⬝ᵥ (blockSel B i *ᵥ w) = (fun a => w (i, a)) ⬝ᵥ (B i *ᵥ fun a => w (i, a)) := by
  simp only [dotProduct, mulVec, blockSel, of_apply, Fintype.sum_prod_type]
  simp [ite_and, Finset.mul_sum]

theorem g69a2_blockAll_mulVec {m n : ℕ} (Z : Matrix (Fin n) (Fin n) ℝ)
    (w : Fin m × Fin n → ℝ) :
    blockAll Z *ᵥ w = fun r => (Z *ᵥ ∑ i, fun a => w (i, a)) r.2 := by
  ext r
  simp only [mulVec, dotProduct, blockAll, of_apply, Fintype.sum_prod_type, Finset.sum_apply,
    Finset.mul_sum]
  rw [Finset.sum_comm]

theorem g69a2_blockAll_quad {m n : ℕ} (Z : Matrix (Fin n) (Fin n) ℝ)
    (w : Fin m × Fin n → ℝ) :
    w ⬝ᵥ (blockAll Z *ᵥ w) = (∑ i, fun a => w (i, a)) ⬝ᵥ (Z *ᵥ ∑ i, fun a => w (i, a)) := by
  rw [g69a2_blockAll_mulVec]
  simp only [dotProduct, Fintype.sum_prod_type, Finset.sum_apply, Finset.sum_mul]
  rw [Finset.sum_comm]


/-- Ben-Tal–Nemirovski, statement (D), p. 267 (setting of Problem (O), p. 265:
`Wᵢ = {x | xᵀBᵢx ≤ 1}`, `Bᵢ ≻ 0`). Let a positive definite `n × n` matrix `Z` be such that the
optimal value of the semidefinite program
`max_X { Tr(M[Z]X) | Tr(BⁱX) ≤ 1, i = 1, …, m, X ⪰ 0 }`   (SDP)
is `≤ 1`, i.e. every feasible `X` has `Tr(M[Z]X) ≤ 1`. Then the ellipsoid `W[Z] = {x | xᵀZx ≤ 1}`
contains the arithmetic sum `W₁ + ⋯ + W_m`. -/
theorem solution {m n : ℕ} (B : Fin m → Matrix (Fin n) (Fin n) ℝ)
    (hB : ∀ i, (B i).PosDef) (Z : Matrix (Fin n) (Fin n) ℝ) (hZ : Z.PosDef)
    (hval : ∀ X : Matrix (Fin m × Fin n) (Fin m × Fin n) ℝ, DFeasible B X →
      (blockAll Z * X).trace ≤ 1) :
    minkowskiSum (fun i => quadSet (B i)) ⊆ quadSet Z := by
  rintro x ⟨w, hw, rfl⟩
  set W : Fin m × Fin n → ℝ := fun r => w r.1 r.2 with hW
  have hX : DFeasible B (vecMulVec W W) := by
    refine ⟨fun i => ?_, ?_⟩
    · rw [mul_vecMulVec, trace_vecMulVec, dotProduct_comm, g69a2_blockSel_quad]
      exact hw i
    · simpa using posSemidef_vecMulVec_self_star W
  have := hval _ hX
  rw [mul_vecMulVec, trace_vecMulVec, dotProduct_comm, g69a2_blockAll_quad] at this
  exact this

