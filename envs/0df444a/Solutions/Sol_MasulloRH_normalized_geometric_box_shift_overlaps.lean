-- Prove2me | solution 1 for MasulloRH.normalized_geometric_box_shift_overlaps
-- status  : ACCEPTED   (prove)
-- author  : @Yi
-- created : 2026-11-21T02:16:20.641275+00:00
-- url     : https://prove2.me/submissions/d28fe29e-b39e-4c04-8bf6-8dd9d9f522ac

import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp

open Filter Finset
open scoped Topology

private theorem denominator_pos (r : ℝ) (hr : 0 ≤ r) (N : ℕ) :
    0 < ∑ j ∈ range (N+1), r^j := by
  apply Finset.sum_pos'
  · intro j _; positivity
  · exact ⟨0, by simp, by simp⟩

private theorem coordinate_limit (r : ℝ) (hr : 0 < r) (hr' : r < 1) (d : ℕ) :
    Tendsto (fun N : ℕ => ∑ j ∈ range (N+1-d),
      (r^j / (∑ k ∈ range (N+1), r^k)) *
      (r^(j+d) / (∑ k ∈ range (N+1), r^k)))
      atTop (𝓝 (r^d * ((1-r)/(1+r)))) := by
  have hsum := (hasSum_geometric_of_lt_one hr.le hr').tendsto_sum_nat
  have hs2 := (hasSum_geometric_of_lt_one (sq_nonneg r) (by nlinarith : r^2<1)).tendsto_sum_nat
  have hN : Tendsto (fun n : ℕ => n+1) atTop atTop := by
    exact tendsto_atTop.2 fun b => Filter.eventually_atTop.2 ⟨b, fun n hn => by omega⟩
  have hNd : Tendsto (fun n : ℕ => n+1-d) atTop atTop := by
    exact tendsto_atTop.2 fun b => Filter.eventually_atTop.2 ⟨b+d, fun n hn => by omega⟩
  have hd0 : (1-r)⁻¹ ≠ 0 := inv_ne_zero (by linarith)
  have H := ((tendsto_const_nhds (x := r^d)).mul (hs2.comp hNd)).div
    ((hsum.comp hN).pow 2) (pow_ne_zero 2 hd0)
  convert H using 1
  · ext N
    simp only [Function.comp_apply, Pi.div_apply, div_eq_mul_inv, Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j hj
    rw [pow_add, ← pow_mul, Nat.mul_comm 2 j, pow_mul, pow_two]
    ring
  · congr 1
    have h1 : 1-r ≠ 0 := by linarith
    have h2 : 1-r^2 ≠ 0 := by nlinarith
    have h3 : 1+r ≠ 0 := by linarith
    field_simp [h1,h2,h3]
    ring

theorem solution {ι : Type*} [Fintype ι] [DecidableEq ι] (r : ι → ℝ)
    (hr : ∀ i, 0 < r i) (hr' : ∀ i, r i < 1) :
    let w (N : ℕ) (x : ι → ℕ) := ∏ i, (r i)^(x i) / (∑ k ∈ range (N+1), (r i)^k)
    (∀ N, (∑ x ∈ Fintype.piFinset (fun _ : ι => range (N+1)), w N x) = 1) ∧
    (∀ d : ι → ℕ, Tendsto (fun N : ℕ => ∑ x ∈ Fintype.piFinset (fun i => range (N+1-d i)),
      w N x * w N (fun i => x i + d i)) atTop
      (𝓝 (∏ i, (r i)^(d i) * ((1-r i)/(1+r i))))) := by
  classical
  dsimp only
  constructor
  · intro N
    rw [← Finset.prod_univ_sum (fun _ : ι => range (N+1)) (fun i (j : ℕ) => (r i)^j / (∑ k ∈ range (N+1), (r i)^k))]
    apply Finset.prod_eq_one
    intro i _
    simp only [div_eq_mul_inv, ← Finset.sum_mul]
    exact mul_inv_cancel₀ (denominator_pos _ (hr i).le N).ne'
  · intro d
    have H := tendsto_finsetProd (s := (Finset.univ : Finset ι))
      (fun i _ => coordinate_limit (r i) (hr i) (hr' i) (d i))
    convert H using 1
    ext N
    simp only [← Finset.prod_mul_distrib]
    exact (Finset.prod_univ_sum (fun i => range (N+1-d i)) (fun i (j : ℕ) => ((r i)^j / (∑ k ∈ range (N+1), (r i)^k)) * ((r i)^(j+d i) / (∑ k ∈ range (N+1), (r i)^k)))).symm
