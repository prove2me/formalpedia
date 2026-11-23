-- Prove2me | solution 1 for GroupTheoreticShannonCapacity.P0Matrix.p0_sign_property
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:49:37.325122+00:00
-- url     : https://prove2.me/submissions/8a5ac0ec-68b5-4745-b0f3-663b2f1df526

import Mathlib.Topology.Instances.Matrix
import Definitions.Def_GroupTheoreticShannonCapacity_Lattice
import Definitions.Def_GroupTheoreticShannonCapacity_Basic
import Definitions.Def_GroupTheoreticShannonCapacity_P0Matrix
import Theorems.Thm_GroupTheoreticShannonCapacity_P0Matrix_isP0_principalSubmatrix
import Theorems.Thm_GroupTheoreticShannonCapacity_P0Matrix_principalSubmatrix_mulVec
import Theorems.Thm_GroupTheoreticShannonCapacity_P0Matrix_p0_add_pos_diagonal_det_pos

set_option autoImplicit true
open GroupTheoreticShannonCapacity GroupTheoreticShannonCapacity.P0Matrix
open Matrix Finset
namespace GroupTheoreticShannonCapacity.P0Matrix
theorem _root_.solution (n : ℕ) (M : Matrix (Fin n) (Fin n) ℝ) (hM : IsP0Matrix n M)
    (x : Fin n → ℝ) (hx : x ≠ 0) :
    ∃ i : Fin n, x i ≠ 0 ∧ (M.mulVec x) i * x i ≥ 0 := by
  -- Proof by contradiction
  by_contra hcontra
  push_neg at hcontra
  -- hcontra : ∀ i, x i = 0 ∨ (M.mulVec x) i * x i < 0

  -- Step 1: Define support S = {i : x i ≠ 0}
  let S := Finset.filter (fun i => x i ≠ 0) Finset.univ
  have hS_nonempty : S.Nonempty := by
    by_contra hS_empty
    rw [Finset.not_nonempty_iff_eq_empty] at hS_empty
    apply hx
    ext i
    have : i ∉ S := by rw [hS_empty]; exact Finset.notMem_empty i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_not, S] at this
    exact this
  -- Step 2: For all i ∈ S, we have (Mx)_i * x_i < 0
  have hsign : ∀ i ∈ S, (M.mulVec x) i * x i < 0 := by
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, S] at hi
    exact hcontra i hi
  -- Step 3: M_S is P₀
  have hMS : IsP0Matrix S.card (principalSubmatrix n M S) :=
    isP0_principalSubmatrix n M hM S
  -- Step 4: Define x_S : Fin S.card → ℝ
  let xS : Fin S.card → ℝ := x ∘ S.orderEmbOfFin rfl
  -- Step 5: xS is never zero (all entries of x on S are nonzero)
  have hxS_ne : ∀ i : Fin S.card, xS i ≠ 0 := fun i => by
    simp only [xS, Function.comp_apply]
    have hmem := Finset.orderEmbOfFin_mem S rfl i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, S] at hmem
    exact hmem
  -- Step 6: (M_S * x_S)_i * (x_S)_i < 0 for all i
  have hxS_supp : ∀ i, i ∉ S → x i = 0 := by
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_not, S] at hi
    exact hi
  have hsignS : ∀ i : Fin S.card,
      (principalSubmatrix n M S).mulVec xS i * xS i < 0 := fun i => by
    rw [principalSubmatrix_mulVec n M S x hxS_supp]
    simp only [xS, Function.comp_apply]
    exact hsign (S.orderEmbOfFin rfl i) (Finset.orderEmbOfFin_mem S rfl i)
  -- Step 7: Define d_j = -(M_S x_S)_j / (x_S)_j > 0
  let d : Fin S.card → ℝ := fun j => -((principalSubmatrix n M S).mulVec xS j) / xS j
  have hd_pos : ∀ j, 0 < d j := fun j => by
    simp only [d]
    -- (M_S x_S)_j * x_S j < 0 with x_S j ≠ 0
    have hsj := hsignS j
    have hxj := hxS_ne j
    by_cases hx_pos : xS j > 0
    · -- xS j > 0, so (M_S xS)_j < 0 (since product < 0)
      have hMx_neg : (principalSubmatrix n M S).mulVec xS j < 0 := by
        by_contra h
        push_neg at h
        have : (principalSubmatrix n M S).mulVec xS j * xS j ≥ 0 :=
          mul_nonneg h (le_of_lt hx_pos)
        linarith
      rw [neg_div, neg_pos]
      exact div_neg_of_neg_of_pos hMx_neg hx_pos
    · push_neg at hx_pos
      have hx_neg : xS j < 0 := lt_of_le_of_ne hx_pos (fun h => hxj h)
      -- xS j < 0, so (M_S xS)_j > 0 (since product < 0)
      have hMx_pos : (principalSubmatrix n M S).mulVec xS j > 0 := by
        by_contra h
        push_neg at h
        have hprod : (principalSubmatrix n M S).mulVec xS j * xS j ≥ 0 :=
          mul_nonneg_of_nonpos_of_nonpos h (le_of_lt hx_neg)
        linarith
      rw [neg_div, neg_pos]
      exact div_neg_of_pos_of_neg hMx_pos hx_neg
  -- Step 8: A = M_S + diag(d) satisfies A x_S = 0
  let A := principalSubmatrix n M S + Matrix.diagonal d
  have hA_xS : A.mulVec xS = 0 := by
    ext j
    simp only [A, Matrix.add_mulVec, Pi.add_apply, Pi.zero_apply, Matrix.mulVec_diagonal]
    simp only [d]
    have hxj := hxS_ne j
    -- Need: (M_S xS)_j + (-(M_S xS)_j / xS_j) * xS_j = 0
    -- The goal is: (M_S xS)_j + (-(M_S xS)_j / xS_j * xS_j) = 0
    rw [div_mul_cancel₀ _ hxj, add_neg_cancel]
  -- Step 9: det(A) = 0 since A x_S = 0 and x_S ≠ 0
  have hS_card_pos : 0 < S.card := hS_nonempty.card_pos
  have hxS_ne_zero : xS ≠ 0 := fun h => by
    have h0 := congr_fun h ⟨0, hS_card_pos⟩
    exact hxS_ne _ h0
  have hdet_zero : A.det = 0 := by
    rw [← Matrix.exists_mulVec_eq_zero_iff]
    exact ⟨xS, hxS_ne_zero, hA_xS⟩
  -- Step 10: But det(A) > 0 by p0_add_pos_diagonal_det_pos
  have hdet_pos : A.det > 0 := p0_add_pos_diagonal_det_pos S.card
    (principalSubmatrix n M S) hMS d hd_pos
  -- Contradiction
  linarith
end GroupTheoreticShannonCapacity.P0Matrix
