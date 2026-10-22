-- Prove2me | solution 1 for NatureSLT.Margin.margin_vc_dim_bound
-- status  : ACCEPTED   (disprove)
-- author  : @fizzyinc3
-- created : 2026-10-21T15:45:52.426883+00:00
-- url     : https://prove2.me/submissions/136ad289-c2a3-4fa4-9f47-98443d5024d0

import Mathlib
import Definitions.Def_NatureSLT_Margin_marginVCDim
open NatureSLT.Margin
open scoped InnerProductSpace

noncomputable def g70slt_v : Fin 3 → EuclideanSpace ℝ (Fin 2) :=
  ![!₂[0, 4], !₂[-2 * Real.sqrt 3, -2], !₂[2 * Real.sqrt 3, -2]]

theorem g70slt_inner_eq {n : ℕ} (u v : EuclideanSpace ℝ (Fin n)) :
    ⟪u, v⟫_ℝ = ∑ j, u j * v j := by
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
  exact Finset.sum_congr rfl (fun j _ => mul_comm _ _)

theorem g70slt_ip (k j : Fin 3) :
    ⟪g70slt_v k, g70slt_v j⟫_ℝ = if k = j then 16 else -8 := by
  have h3 : Real.sqrt 3 * Real.sqrt 3 = 3 := Real.mul_self_sqrt (by norm_num)
  fin_cases k <;> fin_cases j <;>
    rw [g70slt_inner_eq] <;> simp [g70slt_v, Fin.sum_univ_two] <;> nlinarith [h3]

theorem g70slt_vnorm (k : Fin 3) : ‖g70slt_v k‖ = 4 := by
  have h := g70slt_ip k k
  rw [if_pos rfl, real_inner_self_eq_norm_sq] at h
  have : (0:ℝ) ≤ ‖g70slt_v k‖ := norm_nonneg _
  nlinarith

theorem g70slt_wip (s : ℝ) (k j : Fin 3) :
    ⟪(s / 4) • g70slt_v k, g70slt_v j⟫_ℝ = s * (if k = j then 4 else -2) := by
  rw [real_inner_smul_left, g70slt_ip]; split_ifs <;> ring

theorem g70slt_wnorm (s : ℝ) (hs : |s| = 1) (k : Fin 3) : ‖(s / 4) • g70slt_v k‖ = 1 := by
  rw [norm_smul, g70slt_vnorm, Real.norm_eq_abs, abs_div, hs]; norm_num

theorem g70slt_shat : MarginShatters 3 g70slt_v := by
  intro y
  have key : ∀ (s b : ℝ) (k : Fin 3), |s| = 1 →
      (∀ i, (y i = true → 3 ≤ s * (if k = i then 4 else -2) - b) ∧
        (y i = false → s * (if k = i then 4 else -2) - b ≤ -3)) →
      ∃ (w : EuclideanSpace ℝ (Fin 2)) (b : ℝ), ‖w‖ = 1 ∧
        ∀ i, MarginClassifies w b 3 (g70slt_v i) (y i) := by
    intro s b k hs h
    refine ⟨(s / 4) • g70slt_v k, b, g70slt_wnorm s hs k, fun i => ?_⟩
    unfold MarginClassifies
    rw [g70slt_wip]; exact h i
  cases h0 : y 0 <;> cases h1 : y 1 <;> cases h2 : y 2
  · exact key 1 10 0 (by norm_num) (fun i => by fin_cases i <;> simp [h0, h1, h2] <;> norm_num)
  · exact key 1 1 2 (by norm_num) (fun i => by fin_cases i <;> simp [h0, h1, h2] <;> norm_num)
  · exact key 1 1 1 (by norm_num) (fun i => by fin_cases i <;> simp [h0, h1, h2] <;> norm_num)
  · exact key (-1) (-1) 0 (by norm_num) (fun i => by fin_cases i <;> simp [h0, h1, h2] <;> norm_num)
  · exact key 1 1 0 (by norm_num) (fun i => by fin_cases i <;> simp [h0, h1, h2] <;> norm_num)
  · exact key (-1) (-1) 1 (by norm_num) (fun i => by fin_cases i <;> simp [h0, h1, h2] <;> norm_num)
  · exact key (-1) (-1) 2 (by norm_num) (fun i => by fin_cases i <;> simp [h0, h1, h2] <;> norm_num)
  · exact key 1 (-10) 0 (by norm_num) (fun i => by fin_cases i <;> simp [h0, h1, h2] <;> norm_num)

theorem solution : ¬ (∀ {n : ℕ} (X : Set (EuclideanSpace ℝ (Fin n)))
    (c : EuclideanSpace ℝ (Fin n)) (R Δ : ℝ) (hR : 0 < R) (hΔ : 0 < Δ)
    (hX : X ⊆ Metric.closedBall c R),
    marginVCDim X Δ ≤ ((min ⌊R ^ 2 / Δ ^ 2⌋₊ n + 1 : ℕ) : ℕ∞)) := by
  intro H
  have h := H (n := 2) (Metric.closedBall 0 4) 0 4 3 (by norm_num) (by norm_num) subset_rfl
  have hfl : ⌊(4:ℝ) ^ 2 / 3 ^ 2⌋₊ = 1 := by
    rw [Nat.floor_eq_iff (by positivity)]; norm_num
  rw [hfl] at h
  have h3 : ((3 : ℕ) : ℕ∞) ≤ marginVCDim (Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 4) 3 :=
    le_iSup₂_of_le (f := fun (h : ℕ) (_ : ∃ x : Fin h → EuclideanSpace ℝ (Fin 2),
      (∀ i, x i ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 4) ∧ MarginShatters 3 x) =>
        (h : ℕ∞)) 3
      ⟨g70slt_v, fun i => by simp [g70slt_vnorm], g70slt_shat⟩ le_rfl
  have := h3.trans h
  norm_num at this
