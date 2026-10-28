-- Prove2me | solution 2 for MarkovMixing.vecMul_pow
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-27T04:54:07.236092+00:00
-- url     : https://prove2.me/submissions/53dd5729-cf9d-4692-9bf7-26f02d73c848

import Mathlib
import Definitions.Def_mm_spectral
import Theorems.Thm_MarkovChain_vecMul_pow_of_isStationary

open scoped BigOperators
open scoped Matrix
open MarkovMixing
set_option maxHeartbeats 1000000
variable {V : Type*} [Fintype V] [DecidableEq V]

-- `MarkovMixing.IsStationary` and `MarkovChain.IsStationary` are the same condition written
-- twice: a distribution (nonnegative, total mass one -- the standard simplex) fixed by the
-- transition matrix acting on the right.
theorem solution {P : Matrix V V ℝ} {π : V → ℝ} (hπ : IsStationary P π) :
    ∀ t : ℕ, Matrix.vecMul π (P ^ t) = π := by
  have hsimplex : π ∈ stdSimplex ℝ V := ⟨hπ.1.1, hπ.1.2⟩
  exact fun t => MarkovChain.vecMul_pow_of_isStationary ⟨hsimplex, hπ.2⟩ t
