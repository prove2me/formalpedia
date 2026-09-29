-- Prove2me | solution 1 for Komlos.spencer_six_deviations
-- status  : ACCEPTED   (prove)
-- author  : @Hartmann_Psi
-- created : 2026-09-08T23:47:24.348645+00:00
-- url     : https://prove2.me/submissions/b71233df-1f6c-4204-bfa3-ac39493d6a47

import Mathlib
import Definitions.Def_Komlos_model
import Theorems.Thm_Komlos_spencer_partial_coloring
import Theorems.Thm_Komlos_spencer_random_finish
import Theorems.Thm_Komlos_spencer_recursion

open Finset

/-- Spencer's theorem is the recursion fed with the partial colouring step and
the residual colouring. -/
theorem solution (n : ℕ) (A : Fin n → Fin n → ℝ)
    (h01 : ∀ i j, A i j = 0 ∨ A i j = 1) :
    ∃ ε : Fin n → ℝ, Komlos.IsSignVector ε ∧
      ∀ i, |∑ j, A i j * ε j| ≤ 6 * Real.sqrt n :=
  Komlos.spencer_recursion
    (fun n A h01 T hT θ ν hθ0 hθ1 hν hb =>
      Komlos.spencer_partial_coloring n A h01 T hT θ ν hθ0 hθ1 hν hb)
    (fun n hn A h01 T => Komlos.spencer_random_finish n hn A h01 T)
    n A h01
