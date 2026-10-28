-- Prove2me | solution 1 for MarkovMixing.innerPi_comm
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-27T01:08:23.838514+00:00
-- url     : https://prove2.me/submissions/1d062851-8676-491c-ad97-21f5b9507b11

import Mathlib
import Definitions.Def_mm_spectral

-- carved verbatim out of submission b36a2a77-0ed1-410e-b982-dafb4dc643a6, lines 553-555

section
open scoped BigOperators
open scoped Matrix
open MarkovMixing
set_option maxHeartbeats 1000000
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem solution (π g h : V → ℝ) : innerPi π g h = innerPi π h g :=
  Finset.sum_congr rfl fun x _ => by ring

end
