-- Prove2me | solution 1 for MarkovMixing.vecMul_pow
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-27T01:08:22.56174+00:00
-- url     : https://prove2.me/submissions/76773b90-e388-4e3a-9ae1-d6d2df36900a

import Mathlib
import Definitions.Def_mm_spectral

-- carved verbatim out of submission b36a2a77-0ed1-410e-b982-dafb4dc643a6, lines 529-535

section
open scoped BigOperators
open scoped Matrix
open MarkovMixing
set_option maxHeartbeats 1000000
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem solution {P : Matrix V V ℝ} {π : V → ℝ} (hπ : IsStationary P π) :
    ∀ t : ℕ, Matrix.vecMul π (P ^ t) = π := by
  intro t
  induction t with
  | zero => simp
  | succ t ih => rw [pow_succ, ← Matrix.vecMul_vecMul, ih, hπ.2]

end
