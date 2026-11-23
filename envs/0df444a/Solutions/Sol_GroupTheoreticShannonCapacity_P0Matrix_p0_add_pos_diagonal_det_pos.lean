-- Prove2me | solution 1 for GroupTheoreticShannonCapacity.P0Matrix.p0_add_pos_diagonal_det_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:47:13.741269+00:00
-- url     : https://prove2.me/submissions/eda3f051-4345-4c76-af1b-1da180fa49d0

import Mathlib.Topology.Instances.Matrix
import Definitions.Def_GroupTheoreticShannonCapacity_Lattice
import Definitions.Def_GroupTheoreticShannonCapacity_Basic
import Definitions.Def_GroupTheoreticShannonCapacity_P0Matrix
import Theorems.Thm_GroupTheoreticShannonCapacity_P0Matrix_det_add_diagonal
import Theorems.Thm_GroupTheoreticShannonCapacity_P0Matrix_principalSubmatrix_empty_det

set_option autoImplicit true
open GroupTheoreticShannonCapacity GroupTheoreticShannonCapacity.P0Matrix
open Matrix Finset
namespace GroupTheoreticShannonCapacity.P0Matrix
theorem _root_.solution (n : ℕ) (M : Matrix (Fin n) (Fin n) ℝ)
    (hM : IsP0Matrix n M) (d : Fin n → ℝ) (hd : ∀ i, 0 < d i) :
    0 < (M + diagonal d).det := by
  rw [det_add_diagonal]
  -- The sum has a positive term (S = ∅) and all nonnegative terms
  have hempty : (principalSubmatrix n M ∅).det * ∏ i ∈ (∅ : Finset (Fin n))ᶜ, d i =
      ∏ i : Fin n, d i := by
    simp only [principalSubmatrix_empty_det, one_mul, Finset.compl_empty]
  have hprod_pos : 0 < ∏ i : Fin n, d i := Finset.prod_pos (fun i _ => hd i)
  -- Show sum is ≥ the empty set term which is positive
  have hterms_nonneg : ∀ S : Finset (Fin n),
      0 ≤ (principalSubmatrix n M S).det * ∏ i ∈ Sᶜ, d i := fun S => by
    apply mul_nonneg (hM S)
    apply Finset.prod_nonneg
    intro i _
    exact le_of_lt (hd i)
  calc (∑ S : Finset (Fin n), (principalSubmatrix n M S).det * ∏ i ∈ Sᶜ, d i)
      ≥ (principalSubmatrix n M ∅).det * ∏ i ∈ (∅ : Finset (Fin n))ᶜ, d i :=
        Finset.single_le_sum (fun S _ => hterms_nonneg S) (Finset.mem_univ ∅)
    _ = ∏ i : Fin n, d i := hempty
    _ > 0 := hprod_pos
end GroupTheoreticShannonCapacity.P0Matrix
