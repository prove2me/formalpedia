-- Prove2me | solution 1 for GeomDL.RNN.shift_equivariant_s_steps
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-21T19:33:58.121083+00:00
-- url     : https://prove2.me/submissions/7efd8f36-41bf-4ef8-a07e-aef2e22dca21

import Mathlib
import Definitions.Def_GeomDL_RNN_Recurrence

open GeomDL.RNN

theorem solution {k m : ℕ}
    (R : (Fin k → ℝ) → (Fin m → ℝ) → (Fin m → ℝ))
    (h0 : Fin m → ℝ) (z : ℕ → Fin k → ℝ)
    (delay s : ℕ) (hpad : s ≤ delay) (hfix : R 0 h0 = h0) :
    ∀ t : ℕ,
      run R h0 (fun u => pad delay z (u + s)) t =
        run R h0 (pad delay z) (t + s) := by
  have hpre : ∀ j, j ≤ delay → run R h0 (pad delay z) j = h0 := by
    intro j
    induction j with
    | zero => intro _; rfl
    | succ j ih =>
      intro hj
      show R (pad delay z (j + 1)) (run R h0 (pad delay z) j) = h0
      rw [ih (by omega), show pad delay z (j + 1) = 0 by simp [pad, hj]]
      exact hfix
  intro t
  induction t with
  | zero => simp only [zero_add]; rw [hpre s hpad]; rfl
  | succ t ih =>
    show R (pad delay z (t + 1 + s)) (run R h0 (fun u => pad delay z (u + s)) t) =
      run R h0 (pad delay z) (t + 1 + s)
    rw [ih, show t + 1 + s = (t + s) + 1 by ring]
    rfl
