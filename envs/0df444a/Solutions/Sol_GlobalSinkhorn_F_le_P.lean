-- Prove2me | solution 1 for GlobalSinkhorn.F_le_P
-- status  : ACCEPTED   (prove)
-- author  : @涼宮 ハルヒ
-- created : 2026-11-12T13:27:40.250197+00:00
-- url     : https://prove2.me/submissions/46295df3-9181-4d0f-8a3b-08b775a063c7

import Definitions.Def_GlobalSinkhorn_Fw
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

set_option autoImplicit false
open Matrix
open scoped BigOperators
open GlobalSinkhorn

private lemma weighted_pos {n : ℕ} (c v : Fin n → ℝ)
    (hc : ∀ i, 0 ≤ c i) (hs : ∑ i, c i = 1) (hv : ∀ i, 0 < v i) :
    0 < ∑ i, c i * v i := by
  have hcpos : 0 < ∑ i, c i := by rw [hs]; norm_num
  obtain ⟨i, hi, hci⟩ := (Finset.sum_pos_iff_of_nonneg (fun i _ => hc i)).mp hcpos
  exact Finset.sum_pos' (fun i _ => mul_nonneg (hc i) (hv i).le)
    ⟨i, hi, mul_pos hci (hv i)⟩

private lemma inv_weighted_le {n : ℕ} (c v : Fin n → ℝ)
    (hc : ∀ i, 0 ≤ c i) (hs : ∑ i, c i = 1) (hv : ∀ i, 0 < v i) :
    (∑ i, c i * v i)⁻¹ ≤ ∑ i, c i * (v i)⁻¹ := by
  have hpos := weighted_pos c v hc hs hv
  have hcs := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul (Finset.univ : Finset (Fin n))
    (r := c) (f := fun i => c i * v i) (g := fun i => c i * (v i)⁻¹)
    (fun i _ => mul_nonneg (hc i) (hv i).le)
    (fun i _ => mul_nonneg (hc i) (inv_nonneg.mpr (hv i).le))
    (fun i _ => le_of_eq (by field_simp [(hv i).ne'] <;> ring))
  rw [hs] at hcs
  norm_num only [one_pow] at hcs
  rw [← one_div]
  exact (div_le_iff₀ hpos).mpr (by simpa only [mul_comm] using hcs)

private lemma sw_pos {n : ℕ} (S : Matrix (Fin n) (Fin n) ℝ)
    (hS : S ∈ doublyStochastic ℝ (Fin n)) (w : Fin n → ℝ) (hw : ∀ j, 0 < w j) :
    ∀ i, 0 < (S *ᵥ w) i := by
  intro i
  exact weighted_pos (S i) w (fun _ => nonneg_of_mem_doublyStochastic hS)
    (sum_row_of_mem_doublyStochastic hS i) hw

private lemma fw_pos {n : ℕ} (S : Matrix (Fin n) (Fin n) ℝ)
    (hS : S ∈ doublyStochastic ℝ (Fin n)) (w : Fin n → ℝ) (hw : ∀ j, 0 < w j) :
    ∀ j, 0 < Fw S w j := by
  intro j
  apply inv_pos.mpr
  exact weighted_pos (fun i => S i j) (fun i => ((S *ᵥ w) i)⁻¹)
    (fun _ => nonneg_of_mem_doublyStochastic hS)
    (sum_col_of_mem_doublyStochastic hS j) (fun i => inv_pos.mpr (sw_pos S hS w hw i))

theorem solution {n : ℕ} (hn : 0 < n) (S : Matrix (Fin n) (Fin n) ℝ)
    (hS : S ∈ doublyStochastic ℝ (Fin n)) (w : Fin n → ℝ) (hw : ∀ j, 0 < w j) :
    (∀ i, 0 < (S *ᵥ w) i) ∧ (∀ j, 0 < Fw S w j) ∧
      (∀ j, Fw S w j ≤ ((Sᵀ * S) *ᵥ w) j) ∧
      ∀ j, (Fw S w j)⁻¹ ≤ ((Sᵀ * S) *ᵥ (fun k => (w k)⁻¹)) j := by
  have hp := sw_pos S hS w hw
  refine ⟨hp, fw_pos S hS w hw, ?_, ?_⟩
  · intro j
    rw [← Matrix.mulVec_mulVec w Sᵀ S]
    simpa only [Fw, Matrix.mulVec, dotProduct, Matrix.transpose_apply,
      inv_inv] using inv_weighted_le (fun i => S i j) (fun i => ((S *ᵥ w) i)⁻¹)
        (fun _ => nonneg_of_mem_doublyStochastic hS)
        (sum_col_of_mem_doublyStochastic hS j) (fun i => inv_pos.mpr (hp i))
  · intro j
    rw [← Matrix.mulVec_mulVec (fun k => (w k)⁻¹) Sᵀ S]
    simp only [Fw, inv_inv, Matrix.mulVec, dotProduct,
      Matrix.transpose_apply]
    apply Finset.sum_le_sum
    intro i hi
    apply mul_le_mul_of_nonneg_left _ (nonneg_of_mem_doublyStochastic hS)
    exact inv_weighted_le (S i) w (fun _ => nonneg_of_mem_doublyStochastic hS)
      (sum_row_of_mem_doublyStochastic hS i) hw

#print axioms solution