-- Prove2me | solution 1 for GroupTheoreticShannonCapacity.P0Matrix.principalSubmatrix_mul_diagonal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:43:35.710807+00:00
-- url     : https://prove2.me/submissions/779e3165-c9c0-4e3a-aba2-1a669361636d

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
    principalSubmatrix n (M * diagonal d) S =
    principalSubmatrix n M S * diagonal (d ∘ S.orderEmbOfFin rfl) := by
  -- (M*D)_{ij} = M_{ij} * d_j, so the submatrix restricted to S gives M_S * D_S
  unfold principalSubmatrix
  ext i j
  simp only [Matrix.submatrix_apply, Matrix.mul_apply, Matrix.diagonal_apply, Function.comp_apply]
  -- LHS: ∑_k M (S.emb(i)) k * (if k = S.emb(j) then d k else 0)
  -- RHS: ∑_k M (S.emb(i)) (S.emb(k)) * (if k = j then d (S.emb(k)) else 0)
  -- Both simplify to M (S.emb(i)) (S.emb(j)) * d (S.emb(j))
  simp only [mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
end GroupTheoreticShannonCapacity.P0Matrix
