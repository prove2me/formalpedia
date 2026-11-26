-- Prove2me | solution 1 for O3.aboveRestartTrace_exact
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:06:20.147914+00:00
-- url     : https://prove2.me/submissions/402fd326-4193-4458-a98b-1c79a5d5e29e

import Definitions.Def_O3_Foundation
import Definitions.Def_O3_AboveTwo
import Theorems.Thm_O3_abovePhaseTrace_exact

set_option autoImplicit true
open scoped BigOperators
open O3
namespace O3
theorem _root_.solution {d S : ℕ} (oracle : PairOracle d)
    (horizons : Fin S → ℕ)
    (y accelerated : ∀ s, Fin (horizons s) → Vec d) :
    AboveObservationTraceExact oracle
      (aboveRestartTrace oracle horizons y accelerated) := by
  intro observation hobservation
  rw [aboveRestartTrace, List.mem_flatMap] at hobservation
  obtain ⟨s, _, hs⟩ := hobservation
  exact abovePhaseTrace_exact oracle (y s) (accelerated s) observation hs
end O3
