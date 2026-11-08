-- Prove2me | solution 1 for NestedLogitNBR.feasible7_feasibleFull
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T14:30:04.351817+00:00
-- url     : https://prove2.me/submissions/513f1c57-d7e9-43e0-be7d-f024f0a176bb

import Mathlib
import Definitions.Def_NestedLogitNBR_Feasible7
import Definitions.Def_NestedLogitNBR_FeasibleFull

open NestedLogitNBR in
theorem solution {m n : ℕ} (v0 : ℝ) (r v : Fin m → Fin n → ℝ) (γ : Fin m → ℝ)
    (x : ℝ) (y : Fin m → ℝ) (h : Feasible7 v0 r v γ x y) :
    FeasibleFull v0 r v γ x y := by
  refine ⟨h.1, ?_⟩
  intro i S
  have hz := h.2 i (fun j => if j ∈ S then 1 else 0) (by
    intro j
    by_cases hj : j ∈ S
    · simp [hj]
    · simp [hj])
  have e1 : ∑ j, v i j * (if j ∈ S then (1:ℝ) else 0) = prefWeight v i S := by
    simp only [mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_mem, Finset.univ_inter]
    rfl
  have e2 : ∑ j, r i j * v i j * (if j ∈ S then (1:ℝ) else 0) = ∑ j ∈ S, r i j * v i j := by
    simp only [mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_mem, Finset.univ_inter]
  unfold fracObj at hz
  rw [e1, e2] at hz
  unfold nestAttraction nestRevenue
  exact hz
