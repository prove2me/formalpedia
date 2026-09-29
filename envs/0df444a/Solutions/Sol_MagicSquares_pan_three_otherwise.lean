-- Prove2me | solution 1 for MagicSquares.pan_three_otherwise
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-09-18T14:15:44.614913+00:00
-- url     : https://prove2.me/submissions/53ccbacb-9a89-4c97-95fd-e89ca88b825b

import Mathlib
import Definitions.Def_MagicSquares
import Theorems.Thm_MagicSquares_center_of_order_three

set_option autoImplicit false

open MagicSquares
open scoped BigOperators

/-- Solution for `MagicSquares.pan_three_otherwise`.

If a panmagic `3 × 3` square of line sum `t` exists, then in particular it is
magic, so by `center_of_order_three` its centre entry `c` satisfies `3 c = t`.
Hence `3 ∣ t`, and for `t` not divisible by `3` the finset `panMagicSquares 3 t`
is empty, giving `P_3(t) = 0`.

The bridge from panmagic to magic is that the broken diagonals of offset `0` are
the two main diagonals, i.e. `brokenDiagSum M 0 = diagSum M` and
`brokenAntiDiagSum M 0 = antiDiagSum M`. -/
theorem solution (t : ℕ) (ht : ¬ 3 ∣ t) : panMagicCount 3 t = 0 := by
  classical
  rw [panMagicCount, Finset.card_eq_zero]
  apply Finset.not_nonempty_iff_eq_empty.mp
  rintro ⟨M, hM⟩
  have hm : IsPanMagic (fun i j : Fin 3 => (M i j : ℕ)) t := by
    simpa [panMagicSquares] using hM
  have hmagic : IsMagic (fun i j : Fin 3 => (M i j : ℕ)) t :=
    ⟨hm.1,
      by simpa [diagSum, brokenDiagSum] using hm.2.1 (0 : Fin 3),
      by simpa [antiDiagSum, brokenAntiDiagSum] using hm.2.2 (0 : Fin 3)⟩
  have hc := center_of_order_three (fun i j : Fin 3 => (M i j : ℕ)) t hmagic
  exact ht ⟨(M 1 1 : ℕ), hc.symm⟩
