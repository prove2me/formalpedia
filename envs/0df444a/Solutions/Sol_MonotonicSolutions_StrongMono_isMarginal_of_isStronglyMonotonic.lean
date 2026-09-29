-- Prove2me | solution 1 for MonotonicSolutions.StrongMono.isMarginal_of_isStronglyMonotonic
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-28T22:19:07.929854+00:00
-- url     : https://prove2.me/submissions/7e302181-5c80-4bc3-9470-f77370a4876c

import Mathlib
import Definitions.Def_MonotonicSolutions_StrongMono_Game
import Definitions.Def_MonotonicSolutions_StrongMono_Axioms

namespace MonotonicSolutions.StrongMono

end MonotonicSolutions.StrongMono

open MonotonicSolutions.StrongMono

theorem solution {n : ℕ} (φ : Game n → Fin n → ℝ)
    (hφ : IsStronglyMonotonic φ) : IsMarginal φ := by
  intro v w i h
  exact le_antisymm (hφ w v i (fun S => (h S).le)) (hφ v w i (fun S => (h S).ge))
