-- Prove2me | solution 1 for GroupTheoreticShannonCapacity.P0Matrix.principalSubmatrix_diagonal_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:43:32.951282+00:00
-- url     : https://prove2.me/submissions/62c4e22d-2456-4d68-a263-ff9247ec1f5d

import Mathlib.Topology.Instances.Matrix
import Definitions.Def_GroupTheoreticShannonCapacity_Lattice
import Definitions.Def_GroupTheoreticShannonCapacity_Basic
import Definitions.Def_GroupTheoreticShannonCapacity_P0Matrix

set_option autoImplicit true
open GroupTheoreticShannonCapacity GroupTheoreticShannonCapacity.P0Matrix
open Matrix Finset
namespace GroupTheoreticShannonCapacity.P0Matrix
theorem _root_.solution (n : ℕ) (M : Matrix (Fin n) (Fin n) ℝ)
    (d : Fin n → ℝ) (S : Finset (Fin n)) :
    principalSubmatrix n (diagonal d * M) S =
    diagonal (d ∘ S.orderEmbOfFin rfl) * principalSubmatrix n M S := by
  -- (D*M)_{ij} = d_i * M_{ij}, so the submatrix restricted to S gives D_S * M_S
  unfold principalSubmatrix
  ext i j
  simp only [Matrix.submatrix_apply, Matrix.mul_apply, Matrix.diagonal_apply, Function.comp_apply]
  -- LHS: ∑_k (if S.emb(i) = k then d(S.emb(i)) else 0) * M k (S.emb(j))
  -- RHS: ∑_k (if i = k then d(S.emb(i)) else 0) * M (S.emb(k)) (S.emb(j))
  -- Both simplify to d(S.emb(i)) * M (S.emb(i)) (S.emb(j))
  simp only [ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
end GroupTheoreticShannonCapacity.P0Matrix
