-- Prove2me | solution 1 for MaxPressure.FluidStab.input_part_zeroed
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T15:46:51.522287+00:00
-- url     : https://prove2.me/submissions/0cdf1805-1d54-48bb-985a-bd97be1944da

import Mathlib
import Definitions.Def_MaxPressure_FluidStab_Network

set_option autoImplicit false
open MaxPressure.FluidStab Matrix

theorem solution {I J K : ℕ} (N : Network I J K) (hN : N.Standing)
    (h2 : Assumption2 N) :
    ∃ xh : Fin J → ℝ, (∀ j, 0 ≤ xh j) ∧ (∀ i, 0 < (R N *ᵥ xh) i) ∧
      (∀ j, IsInputActivity N j → xh j = 0) ∧
      (∀ k, N.inputProc k → ∑ j, N.A k j * xh j = 0) := by
  classical
  obtain ⟨hAB, hBB, hne, hio, hAk, hproc, hex, hinput, hm, hP, hP00⟩ := hN
  obtain ⟨x, hx0, hxpos⟩ := h2
  let xh : Fin J → ℝ := fun j => if IsInputActivity N j then 0 else x j
  have hRneg : ∀ i j, IsInputActivity N j → R N i j ≤ 0 := by
    intro i j hj
    obtain ⟨hj0, hjs⟩ := hj
    unfold R
    rw [Fin.sum_univ_succ]
    simp only [hj0, hjs, one_mul, zero_mul, Finset.sum_const_zero, add_zero, zero_sub]
    have hμ : 0 < μ N j := by unfold μ; exact one_div_pos.mpr (hm j)
    exact mul_nonpos_of_nonneg_of_nonpos hμ.le (neg_nonpos.mpr (hP j 0 i.succ))
  refine ⟨xh, fun j => ?_, fun i => ?_, fun j hj => ?_, fun k hk => ?_⟩
  · simp only [xh]; split_ifs
    · exact le_refl _
    · exact hx0 j
  · refine lt_of_lt_of_le (hxpos i) ?_
    simp only [mulVec, dotProduct]
    refine Finset.sum_le_sum (fun j _ => ?_)
    simp only [xh]
    split_ifs with h
    · rw [mul_zero]
      exact mul_nonpos_of_nonpos_of_nonneg (hRneg i j h) (hx0 j)
    · exact le_refl _
  · simp [xh, hj]
  · apply Finset.sum_eq_zero
    intro j _
    rcases hAB k j with h | h
    · rw [h, zero_mul]
    · have := (hproc k j h).mp hk
      simp [xh, this]
