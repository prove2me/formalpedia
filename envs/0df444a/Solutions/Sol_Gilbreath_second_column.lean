-- Prove2me | solution 1 for Gilbreath.second_column
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Lucas
-- created : 2026-09-15T20:36:42.052516+00:00
-- url     : https://prove2.me/submissions/af1a3265-15a6-4538-9f10-ad67bdc4265a
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_gilbreath_triangle
import Theorems.Thm_Gilbreath_tail_propagation
import Theorems.Thm_Gilbreath_zero_two_blocks

open Gilbreath

theorem solution (k : ℕ) : d (k + 1) 1 ≤ 2 := by
  -- Some row `j ≥ 1` with `j + m = k + 1` carries a block of `0`s and `2`s at the
  -- indices `1, …, m + 1`.
  obtain ⟨j, m, _hj, hjm, hblock⟩ := zero_two_blocks k
  -- The block propagates along the second column: after `m` differencing steps the
  -- entry at index `1` still lies in `{0, 2}`.
  have hp := tail_propagation (d j) m hblock
  -- Iterating `m` steps from row `j` lands on row `j + m = k + 1`.
  rw [iterAbsDiff_d, hjm] at hp
  omega
