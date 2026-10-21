-- Prove2me | solution 1 for GeometryOfGraphs.FlowCut.l1_coordinate_min
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T20:35:15.396967+00:00
-- url     : https://prove2.me/submissions/f60bca57-f434-4426-a15f-aaa7ff497c4b

import Mathlib
import Definitions.Def_GeometryOfGraphs_FlowCut_Network

set_option autoImplicit false
open GeometryOfGraphs.FlowCut

theorem solution {V : Type*} [Fintype V] [DecidableEq V] (N : Network V) {m : ℕ}
    (x : V → Fin m → ℝ)
    (hpos : 0 < ∑ μ, N.D μ * ∑ r, |x (N.s μ) r - x (N.t μ) r|) :
    ∃ r : Fin m, 0 < ∑ μ, N.D μ * |x (N.s μ) r - x (N.t μ) r| ∧
      ((1 / 2) * ∑ i, ∑ j, N.C i j * |x i r - x j r|) *
          (∑ μ, N.D μ * ∑ r', |x (N.s μ) r' - x (N.t μ) r'|) ≤
        ((1 / 2) * ∑ i, ∑ j, N.C i j * ∑ r', |x i r' - x j r'|) *
          (∑ μ, N.D μ * |x (N.s μ) r - x (N.t μ) r|) := by
  obtain ⟨Bf, hBf⟩ : ∃ B : Fin m → ℝ, ∀ r, B r = ∑ μ, N.D μ * |x (N.s μ) r - x (N.t μ) r| :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨Af, hAf⟩ : ∃ A : Fin m → ℝ,
      ∀ r, A r = (1 / 2) * ∑ i, ∑ j, N.C i j * |x i r - x j r| := ⟨_, fun _ => rfl⟩
  have hBsum : ∑ μ, N.D μ * ∑ r, |x (N.s μ) r - x (N.t μ) r| = ∑ r, Bf r := by
    simp only [hBf, Finset.mul_sum]
    exact Finset.sum_comm
  have hAsum : (1 / 2) * ∑ i, ∑ j, N.C i j * ∑ r, |x i r - x j r| = ∑ r, Af r := by
    simp only [hAf]
    rw [← Finset.mul_sum]
    congr 1
    simp only [Finset.mul_sum]
    calc ∑ i, ∑ j, ∑ r, N.C i j * |x i r - x j r|
        = ∑ i, ∑ r, ∑ j, N.C i j * |x i r - x j r| :=
          Finset.sum_congr rfl (fun i _ => Finset.sum_comm)
      _ = ∑ r, ∑ i, ∑ j, N.C i j * |x i r - x j r| := Finset.sum_comm
  have hApos : ∀ r, 0 ≤ Af r := fun r => by
    rw [hAf]
    exact mul_nonneg (by norm_num) (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
      mul_nonneg (N.C_nonneg i j) (abs_nonneg _))
  have hBnn : ∀ r, 0 ≤ Bf r := fun r => by
    rw [hBf]
    exact Finset.sum_nonneg fun μ _ => mul_nonneg (N.D_nonneg μ) (abs_nonneg _)
  rw [hBsum] at hpos
  have key : ∃ r, 0 < Bf r ∧ Af r * (∑ r', Bf r') ≤ (∑ r', Af r') * Bf r := by
    by_contra hcon
    push_neg at hcon
    obtain ⟨r0, hr0⟩ : ∃ r, 0 < Bf r := by
      by_contra h
      push_neg at h
      have : ∑ r, Bf r ≤ 0 := Finset.sum_nonpos (fun r _ => h r)
      linarith
    have hlt : ∑ r, (∑ r', Af r') * Bf r < ∑ r, Af r * (∑ r', Bf r') := by
      apply Finset.sum_lt_sum
      · intro r _
        by_cases hr : 0 < Bf r
        · exact (hcon r hr).le
        · have : Bf r = 0 := le_antisymm (not_lt.mp hr) (hBnn r)
          rw [this, mul_zero]
          exact mul_nonneg (hApos r) (Finset.sum_nonneg fun r _ => hBnn r)
      · exact ⟨r0, Finset.mem_univ _, hcon r0 hr0⟩
    rw [← Finset.mul_sum, ← Finset.sum_mul] at hlt
    exact lt_irrefl _ hlt
  obtain ⟨r, h1, h2⟩ := key
  refine ⟨r, by rw [← hBf]; exact h1, ?_⟩
  rw [hBsum, hAsum, ← hAf, ← hBf]
  exact h2
