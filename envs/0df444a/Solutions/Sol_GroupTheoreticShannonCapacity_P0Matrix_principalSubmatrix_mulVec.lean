-- Prove2me | solution 1 for GroupTheoreticShannonCapacity.P0Matrix.principalSubmatrix_mulVec
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:43:15.529829+00:00
-- url     : https://prove2.me/submissions/62507e72-ff7f-42b9-83e9-a54e7ce5bad4

import Mathlib.Topology.Instances.Matrix
import Definitions.Def_GroupTheoreticShannonCapacity_Lattice
import Definitions.Def_GroupTheoreticShannonCapacity_Basic
import Definitions.Def_GroupTheoreticShannonCapacity_P0Matrix

set_option autoImplicit true
open GroupTheoreticShannonCapacity GroupTheoreticShannonCapacity.P0Matrix
open Matrix Finset
namespace GroupTheoreticShannonCapacity.P0Matrix
theorem _root_.solution (n : ℕ) (M : Matrix (Fin n) (Fin n) ℝ) (S : Finset (Fin n))
    (x : Fin n → ℝ) (hx_supp : ∀ i, i ∉ S → x i = 0) (i : Fin S.card) :
    (principalSubmatrix n M S).mulVec (x ∘ S.orderEmbOfFin rfl) i =
    (M.mulVec x) (S.orderEmbOfFin rfl i) := by
  unfold principalSubmatrix Matrix.mulVec dotProduct
  simp only [Matrix.submatrix_apply, Function.comp_apply]
  -- LHS: Σ_j M_{S(i), S(j)} * x_{S(j)}
  -- RHS: Σ_k M_{S(i), k} * x_k
  -- We show RHS = Σ_{k ∈ S} M_{S(i), k} * x_k (since x_k = 0 for k ∉ S)
  -- Then reindex to get LHS
  -- First, restrict the RHS sum to S using that x = 0 outside S
  have hRHS : (∑ j : Fin n, M (S.orderEmbOfFin rfl i) j * x j) =
      ∑ j ∈ S, M (S.orderEmbOfFin rfl i) j * x j := by
    rw [← Finset.sum_filter_add_sum_filter_not (s := Finset.univ) (p := (· ∈ S))]
    simp only [Finset.filter_mem_eq_inter, Finset.univ_inter]
    rw [add_comm]
    convert zero_add _ using 2
    apply Finset.sum_eq_zero
    intro k hk
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
    rw [hx_supp k hk, mul_zero]
  rw [hRHS]
  -- Now reindex: sum over S ↔ sum over Fin S.card via orderEmbOfFin
  symm
  rw [Finset.sum_bij (fun j _ => S.orderEmbOfFin rfl j)]
  · intro a _
    exact Finset.orderEmbOfFin_mem S rfl a
  · intro a b _ _ hab
    exact (S.orderEmbOfFin rfl).injective hab
  · intro k hk
    -- Find j ∈ Fin S.card such that S.orderEmbOfFin j = k
    have hk_range : k ∈ Set.range (S.orderEmbOfFin rfl) := by
      rw [Finset.range_orderEmbOfFin]
      exact hk
    obtain ⟨j, hj⟩ := hk_range
    exact ⟨j, Finset.mem_univ j, hj⟩
  · intro a _
    rfl
end GroupTheoreticShannonCapacity.P0Matrix
