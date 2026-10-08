-- Prove2me | solution 1 for MaxPressure.FluidStab.input_column_R_nonpos
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T16:08:22.821313+00:00
-- url     : https://prove2.me/submissions/dbbcbcee-fa66-4507-ab4e-d71596d6f965

import Mathlib
import Definitions.Def_MaxPressure_FluidStab_Network

open MaxPressure.FluidStab Matrix in
theorem solution {I J K : ℕ} (N : Network I J K) (hN : N.Standing)
    (j : Fin J) (hj : IsInputActivity N j) (i : Fin I) :
    R N i j = -(μ N j * N.B j 0 * N.P j 0 i.succ) ∧ R N i j ≤ 0 := by
  obtain ⟨_, _, _, _, _, _, _, _, hm, hP, _⟩ := hN
  obtain ⟨h0, hs⟩ := hj
  have hR : R N i j = -(μ N j * N.B j 0 * N.P j 0 i.succ) := by
    unfold R
    rw [Fin.sum_univ_succ]
    simp only [hs, zero_mul, Finset.sum_const_zero, add_zero, zero_sub]
    ring
  refine ⟨hR, ?_⟩
  rw [hR, h0]
  have hμ : 0 < μ N j := by unfold μ; exact one_div_pos.mpr (hm j)
  have := hP j 0 i.succ
  have : 0 ≤ μ N j * 1 * N.P j 0 i.succ := by positivity
  linarith
