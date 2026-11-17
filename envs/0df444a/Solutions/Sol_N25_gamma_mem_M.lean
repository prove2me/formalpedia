-- Prove2me | solution 1 for N25.gamma_mem_M
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:35:49.491857+00:00
-- url     : https://prove2.me/submissions/c62578cc-e9ad-496c-828a-bfe440e1744e

import Mathlib
import Definitions.Def_N25
import Definitions.Def_N25_LocalKummerEquivariance

set_option autoImplicit false

noncomputable section

namespace N25

/-- The diamond operator preserves the arithmetic Galois fixed subgroup. -/
theorem _root_.solution {x : N25.J} (hx : x ∈ N25.M) : N25.gamma x ∈ N25.M := by
  change ∀ σ : Gal, σ • gamma x = gamma x
  intro σ
  rw [gamma_galois_comm]
  exact congrArg gamma (hx σ)

end N25
