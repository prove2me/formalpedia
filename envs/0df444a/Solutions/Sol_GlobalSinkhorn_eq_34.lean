-- Prove2me | solution 1 for GlobalSinkhorn.eq_34
-- status  : ACCEPTED   (prove)
-- author  : @涼宮 ハルヒ
-- created : 2026-11-13T12:29:33.061561+00:00
-- url     : https://prove2.me/submissions/eeb6667b-6dcf-49d7-b7b3-a8eee59d189b

import Definitions.Def_GlobalSinkhorn_IsPosDiagScaling
import Definitions.Def_GlobalSinkhorn_skIter
import Mathlib.Algebra.Ring.Parity
import Lean.Elab.Tactic.Omega
import Definitions.Def_GlobalSinkhorn_Fw
import Definitions.Def_GlobalSinkhorn_Mw
import Definitions.Def_GlobalSinkhorn_rowNormalize
import Definitions.Def_GlobalSinkhorn_colNormalize
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

private lemma mw_entry {n : ℕ} (S : Matrix (Fin n) (Fin n) ℝ)
    (w : Fin n → ℝ) (i j : Fin n) :
    Mw S w i j = ((S *ᵥ w) i)⁻¹ * S i j * w j := by
  simp [Mw, Matrix.diagonal_mul, Matrix.mul_diagonal]

private lemma col_sum {n : ℕ} (S : Matrix (Fin n) (Fin n) ℝ)
    (w : Fin n → ℝ) (j : Fin n) : ∑ i, Mw S w i j = w j / Fw S w j := by
  simp only [mw_entry, Fw, div_inv_eq_mul, Matrix.mulVec, dotProduct, Matrix.transpose_apply]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  ring

private lemma cycle_all {n : ℕ} (hn : 2 ≤ n) (S : Matrix (Fin n) (Fin n) ℝ)
    (hS : S ∈ doublyStochastic ℝ (Fin n)) (w : Fin n → ℝ) (hw : ∀ j, 0 < w j) :
    Mw S w ∈ Matrix.rowStochastic ℝ (Fin n) ∧
      (∀ j, ∑ i, Mw S w i j = w j / Fw S w j ∧ 0 < w j / Fw S w j) ∧
      rowNormalize (colNormalize (Mw S w)) = Mw S (Fw S w) := by
  have hp := sw_pos S hS w hw
  have hq := fw_pos S hS w hw
  have hr := sw_pos S hS (Fw S w) hq
  have hcol : ∀ i j, colNormalize (Mw S w) i j = ((S *ᵥ w) i)⁻¹ * S i j * Fw S w j := by
    intro i j
    change Mw S w i j / (∑ k, Mw S w k j) = _
    rw [col_sum, mw_entry]
    field_simp [(hp i).ne', (hw j).ne', (hq j).ne']
    <;> ring
  have hrow : ∀ i, ∑ j, colNormalize (Mw S w) i j =
      ((S *ᵥ w) i)⁻¹ * (S *ᵥ Fw S w) i := by
    intro i
    simp only [hcol, Matrix.mulVec, dotProduct, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  refine ⟨?_, ?_, ?_⟩
  · rw [Matrix.mem_rowStochastic_iff_sum]
    constructor
    · intro i j
      rw [mw_entry]
      exact mul_nonneg (mul_nonneg (inv_nonneg.mpr (hp i).le)
        (nonneg_of_mem_doublyStochastic hS)) (hw j).le
    · intro i
      simp only [mw_entry, mul_assoc, ← Finset.mul_sum]
      exact inv_mul_cancel₀ (hp i).ne'
  · intro j
    exact ⟨col_sum S w j, div_pos (hw j) (hq j)⟩
  · ext i j
    change colNormalize (Mw S w) i j / (∑ k, colNormalize (Mw S w) i k) = _
    rw [hrow, hcol, mw_entry]
    field_simp [(hp i).ne', (hr i).ne']
    <;> ring

private lemma mw_initial {n : ℕ} (A S : Matrix (Fin n) (Fin n) ℝ) (x y : Fin n → ℝ)
    (hA : A ∈ Matrix.rowStochastic ℝ (Fin n)) (hxy : IsPosDiagScaling A S x y) :
    Mw S (fun j => (y j)⁻¹) = A := by
  obtain ⟨hx, hy, hxy⟩ := hxy
  have hentry : ∀ i j, S i j = x i * A i j * y j := by
    intro i j
    simpa [Matrix.diagonal_mul, Matrix.mul_diagonal] using
      congrArg (fun M : Matrix (Fin n) (Fin n) ℝ => M i j) hxy
  have hsum : ∀ i, (S *ᵥ (fun j => (y j)⁻¹)) i = x i := by
    intro i
    simp only [Matrix.mulVec, dotProduct, hentry, mul_assoc,
      mul_inv_cancel₀ (ne_of_gt (hy _)), mul_one, ← Finset.mul_sum,
      Matrix.sum_row_of_mem_rowStochastic hA, mul_one]
  ext i j
  rw [mw_entry, hsum, hentry]
  field_simp [(hx i).ne', (hy j).ne']
  <;> ring

theorem solution {n : ℕ} (hn : 2 ≤ n) (A S : Matrix (Fin n) (Fin n) ℝ) (x y : Fin n → ℝ)
    (hA : A ∈ Matrix.rowStochastic ℝ (Fin n))
    (hS : S ∈ doublyStochastic ℝ (Fin n))
    (hxy : IsPosDiagScaling A S x y) (t : ℕ) :
    skIter A (2 * t) = Mw S ((Fw S)^[t] (fun j => (y j)⁻¹)) := by
  have hw : ∀ t j, 0 < ((Fw S)^[t] (fun j => (y j)⁻¹)) j := by
    intro t
    induction t with
    | zero => exact fun j => inv_pos.mpr (hxy.2.1 j)
    | succ t ih => simpa only [Function.iterate_succ_apply'] using (fw_pos S hS _ ih)
  induction t with
  | zero => simpa [skIter] using (mw_initial A S x y hA hxy).symm
  | succ t ih =>
    rw [show 2 * (t + 1) = (2 * t + 1) + 1 by omega, skIter,
      if_neg (by simp [Nat.even_add, Nat.even_mul]), skIter,
      if_pos (by simp [Nat.even_mul]), ih, (cycle_all hn S hS _ (hw t)).2.2,
      Function.iterate_succ_apply']

#print axioms solution


