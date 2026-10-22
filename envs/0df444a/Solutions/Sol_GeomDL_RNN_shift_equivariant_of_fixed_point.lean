-- Prove2me | solution 1 for GeomDL.RNN.shift_equivariant_of_fixed_point
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung
-- created : 2026-10-21T16:01:26.615164+00:00
-- url     : https://prove2.me/submissions/321bca4c-9411-4252-a057-3181c94be0f9

import Mathlib
import Definitions.Def_GeomDL_RNN_Recurrence

open GeomDL.RNN

theorem solution {k m : ℕ}
    (R : (Fin k → ℝ) → (Fin m → ℝ) → (Fin m → ℝ))
    (h0 : Fin m → ℝ) (z : ℕ → Fin k → ℝ)
    (delay : ℕ) (hpad : 1 ≤ delay) (hfix : R 0 h0 = h0) :
    ∀ t : ℕ,
      run R h0 (fun u => pad delay z (u + 1)) t =
        run R h0 (pad delay z) (t + 1) := by
  intro t
  induction t with
  | zero =>
    show h0 = R (pad delay z 1) h0
    rw [pad, if_pos hpad, hfix]
  | succ t ih =>
    show R (pad delay z (t + 1 + 1)) (run R h0 (fun u => pad delay z (u + 1)) t) =
      R (pad delay z (t + 1 + 1)) (run R h0 (pad delay z) (t + 1))
    rw [ih]
