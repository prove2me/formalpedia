-- Prove2me | solution 1 for GroupTheoreticShannonCapacity.P0Matrix.det_add_diagonal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:45:24.870945+00:00
-- url     : https://prove2.me/submissions/95e23f7f-039a-413d-bc37-f1ec54de3b64

import Mathlib.Topology.Instances.Matrix
import Definitions.Def_GroupTheoreticShannonCapacity_Lattice
import Definitions.Def_GroupTheoreticShannonCapacity_Basic
import Definitions.Def_GroupTheoreticShannonCapacity_P0Matrix
import Theorems.Thm_GroupTheoreticShannonCapacity_P0Matrix_prod_ite_sigma_eq
import Theorems.Thm_GroupTheoreticShannonCapacity_P0Matrix_sum_fixing_eq_det

set_option autoImplicit true
open GroupTheoreticShannonCapacity GroupTheoreticShannonCapacity.P0Matrix
open Matrix Finset
namespace GroupTheoreticShannonCapacity.P0Matrix
theorem _root_.solution (n : ℕ) (M : Matrix (Fin n) (Fin n) ℝ) (d : Fin n → ℝ) :
    (M + diagonal d).det =
    ∑ S : Finset (Fin n), (principalSubmatrix n M S).det * ∏ i ∈ Sᶜ, d i := by
  -- Apply Leibniz formula
  rw [Matrix.det_apply']
  -- Each entry (M + diag d)(σ i, i) = M(σ i, i) + (if σ i = i then d i else 0)
  have hentry : ∀ σ : Equiv.Perm (Fin n), ∀ i,
      (M + diagonal d) (σ i) i = M (σ i) i + if σ i = i then d i else 0 := by
    intro σ i
    simp only [Matrix.add_apply, Matrix.diagonal_apply]
    by_cases h : σ i = i
    · simp [h]
    · simp [h]
  conv_lhs =>
    arg 2
    ext σ
    rw [show ∏ i, (M + diagonal d) (σ i) i = ∏ i, (M (σ i) i + if σ i = i then d i else 0)
      from Finset.prod_congr rfl (fun i _ => hentry σ i)]
  -- Expand using prod_add: ∏(a+b) = Σ_T ∏_{T} a * ∏_{Tᶜ} b
  conv_lhs =>
    arg 2
    ext σ
    rw [Finset.prod_add (fun i => M (σ i) i) (fun i => if σ i = i then d i else 0) Finset.univ]
  -- Swap sum over permutations and sum over powerset
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  -- Convert powerset to Finset (Fin n) indexing
  conv_lhs =>
    arg 2
    ext T
    arg 2
    ext σ
    rw [show Finset.univ \ T = Tᶜ by rfl]
  -- Use prod_ite_sigma_eq to simplify the diagonal terms
  conv_lhs =>
    arg 2
    ext T
    arg 2
    ext σ
    rw [show ∏ i ∈ Tᶜ, (if σ i = i then d i else 0) =
        (∏ i ∈ Tᶜ, d i) * ∏ i ∈ Tᶜ, (if σ i = i then (1 : ℝ) else 0) by
      rw [← Finset.prod_mul_distrib]
      apply Finset.prod_congr rfl
      intro i _
      by_cases h : σ i = i <;> simp [h]]
  conv_lhs =>
    arg 2
    ext T
    arg 2
    ext σ
    rw [prod_ite_sigma_eq]
  -- Rearrange multiplications to factor out the product over complement
  conv_lhs =>
    arg 2
    ext T
    arg 2
    ext σ
    -- Rearrange: sign * ((∏_T M) * ((∏_Tᶜ d) * ind)) = sign * (∏_T M) * ind * (∏_Tᶜ d)
    rw [show (Equiv.Perm.sign σ : ℝ) * ((∏ i ∈ T, M (σ i) i) *
        ((∏ i ∈ Tᶜ, d i) * if ∀ i ∈ Tᶜ, σ i = i then 1 else 0)) =
        ((Equiv.Perm.sign σ : ℝ) * (∏ i ∈ T, M (σ i) i) *
        (if ∀ i ∈ Tᶜ, σ i = i then 1 else 0)) * (∏ i ∈ Tᶜ, d i) by ring]
  -- Now factor out the product over complement
  conv_lhs =>
    arg 2
    ext T
    rw [← Finset.sum_mul]
  -- The sum over σ with the indicator becomes sum over fixing permutations
  -- First transform (f * if p then 1 else 0) to (if p then f else 0)
  conv_lhs =>
    arg 2
    ext T
    arg 1
    arg 2
    ext σ
    rw [show ((Equiv.Perm.sign σ : ℝ) * (∏ i ∈ T, M (σ i) i)) *
          (if ∀ i ∈ Tᶜ, σ i = i then (1 : ℝ) else 0) =
        if ∀ i ∈ Tᶜ, σ i = i then (Equiv.Perm.sign σ : ℝ) * ∏ i ∈ T, M (σ i) i else 0 by
      by_cases h : ∀ i ∈ Tᶜ, σ i = i <;> simp]
  -- Now apply Finset.sum_filter
  conv_lhs =>
    arg 2
    ext T
    arg 1
    rw [← Finset.sum_filter]
  -- Apply sum_fixing_eq_det
  conv_lhs =>
    arg 2
    ext T
    arg 1
    rw [sum_fixing_eq_det]
  -- Convert from powerset to Finset indexing
  -- univ.powerset = all Finsets, so the sums are equal
  have hps_eq_univ : (Finset.univ : Finset (Fin n)).powerset = Finset.univ := by
    ext S
    simp only [Finset.mem_powerset, Finset.subset_univ, Finset.mem_univ]
  rw [hps_eq_univ]
end GroupTheoreticShannonCapacity.P0Matrix
