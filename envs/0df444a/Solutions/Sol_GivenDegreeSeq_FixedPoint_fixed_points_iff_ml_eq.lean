-- Prove2me | solution 1 for GivenDegreeSeq.FixedPoint.fixed_points_iff_ml_eq
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T20:30:44.863713+00:00
-- url     : https://prove2.me/submissions/46641c04-d1d4-42dd-9aee-bd14e7c9eb45

import Mathlib
import Definitions.Def_GivenDegreeSeq_FixedPoint_Basic

set_option autoImplicit false
open GivenDegreeSeq.FixedPoint

lemma gdf_r_pos {n : ℕ} (x : Fin n → ℝ) (i j : Fin n) : 0 < r x i j := by
  unfold r; positivity

lemma gdf_S_pos {n : ℕ} (hn : 2 ≤ n) (x : Fin n → ℝ) (i : Fin n) :
    0 < ∑ j ∈ Finset.univ.erase i, r x i j := by
  apply Finset.sum_pos (fun j _ => gdf_r_pos x i j)
  rw [← Finset.card_pos, Finset.card_erase_of_mem (Finset.mem_univ i)]
  simp
  omega

lemma gdf_edgeProb {n : ℕ} (x : Fin n → ℝ) (i j : Fin n) :
    edgeProb x i j = Real.exp (x i) * r x i j := by
  unfold edgeProb r
  have h1 : (0:ℝ) < Real.exp (x j) := Real.exp_pos _
  have h2 : Real.exp (x i + x j) = Real.exp (x i) * Real.exp (x j) := Real.exp_add _ _
  have h3 : Real.exp (-x j) * Real.exp (x j) = 1 := by rw [← Real.exp_add]; simp
  rw [h2]
  field_simp
  nlinarith [h3]

lemma gdf_ml_sum {n : ℕ} (x : Fin n → ℝ) (i : Fin n) :
    ∑ j ∈ Finset.univ.erase i, edgeProb x i j =
      Real.exp (x i) * ∑ j ∈ Finset.univ.erase i, r x i j := by
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl (fun j _ => gdf_edgeProb x i j)

theorem solution {n : ℕ} (hn : 2 ≤ n) (d : Fin n → ℝ) (hd : ∀ i, 0 < d i)
    (x : Fin n → ℝ) :
    phi d x = x ↔ MLEq d x := by
  unfold MLEq
  rw [funext_iff]
  refine forall_congr' (fun i => ?_)
  rw [gdf_ml_sum]
  have hS := gdf_S_pos hn x i
  have hE := Real.exp_pos (x i)
  unfold phi
  constructor
  · intro h
    have : Real.log (d i) = x i + Real.log (∑ j ∈ Finset.univ.erase i, r x i j) := by linarith
    have h2 : Real.log (d i) = Real.log (Real.exp (x i) * ∑ j ∈ Finset.univ.erase i, r x i j) := by
      rw [Real.log_mul hE.ne' hS.ne', Real.log_exp]; exact this
    exact Real.log_injOn_pos (Set.mem_Ioi.2 (hd i)) (Set.mem_Ioi.2 (mul_pos hE hS)) h2
  · intro h
    rw [h, Real.log_mul hE.ne' hS.ne', Real.log_exp]; ring
