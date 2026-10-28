-- Prove2me | solution 1 for MarkovMixing.pow_entry_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-27T01:08:21.905248+00:00
-- url     : https://prove2.me/submissions/668107d9-339a-4002-a951-ab1cb24febf6

import Mathlib
import Definitions.Def_mm_spectral

-- carved verbatim out of submission b36a2a77-0ed1-410e-b982-dafb4dc643a6, lines 517-528

section
open scoped BigOperators
open scoped Matrix
open MarkovMixing
set_option maxHeartbeats 1000000
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem solution {P : Matrix V V ℝ} (hP : IsStochastic P) :
    ∀ (t : ℕ) (x y : V), 0 ≤ (P ^ t) x y := by
  intro t
  induction t with
  | zero =>
    intro x y
    by_cases h : x = y <;> simp [Matrix.one_apply, h]
  | succ t ih =>
    intro x y
    rw [pow_succ, Matrix.mul_apply]
    exact Finset.sum_nonneg fun z _ => mul_nonneg (ih x z) (hP.1 z y)

end
