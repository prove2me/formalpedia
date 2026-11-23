-- Prove2me | solution 1 for GrothendieckLB.Supplement.cq_energy_panel_eighth_derivative_bounds
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-23T21:44:18.581049+00:00
-- url     : https://prove2.me/submissions/57fec77c-0c39-4960-9578-a775c03c7209
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_GrothendieckLB_Supplement_cq_eighth_derivative_le_angular_jets
import Theorems.Thm_GrothendieckLB_Supplement_cq_angular_jet_panel_budget
open GrothendieckLB.Supplement CQBoundary

theorem solution :
    ∃ B : ℕ → ℝ, (∀ i < 1024, ∀ x ∈ Set.Icc (0:ℝ) 1,
      iteratedDeriv 8 (GaussFour.panel i) x ≤ B i) ∧
      (∑ i ∈ Finset.range 1024, B i/1778112000)/1024 ≤ 2.29513648 := by
  obtain ⟨V,hV,hbudget⟩ := cq_angular_jet_panel_budget
  refine ⟨fun i => (Real.pi/1024)^8*jetMajorant (V i),?_,hbudget⟩
  intro i hi x hx
  let θ := (i:ℝ)*(Real.pi/1024)+(Real.pi/1024)*x
  apply (cq_eighth_derivative_le_angular_jets i x).trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  unfold jetMajorant
  apply Finset.sum_le_sum
  intro j hj
  have hj' : j ≤ 8 := by have h := Finset.mem_range.mp hj; omega
  have h8 : 8-j ≤ 8 := Nat.sub_le .. 
  have hn (b k) : 0 ≤ angularJetNorm b k θ := Real.sqrt_nonneg _
  have hp (b : Bool) : angularJetNorm b j θ * angularJetNorm b (8-j) θ ≤ V i b j * V i b (8-j) :=
    mul_le_mul (hV i hi x hx b j hj') (hV i hi x hx b (8-j) h8) (hn ..)
      ((hn ..).trans (hV i hi x hx b j hj'))
  exact mul_le_mul_of_nonneg_left (add_le_add (hp false)
    (mul_le_mul_of_nonneg_left (hp true) (by norm_num))) (Nat.cast_nonneg _)
