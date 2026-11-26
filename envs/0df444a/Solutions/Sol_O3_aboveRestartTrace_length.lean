-- Prove2me | solution 1 for O3.aboveRestartTrace_length
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:06:32.883281+00:00
-- url     : https://prove2.me/submissions/bcd02efc-8d37-4cba-99d8-f5f0eb21ccd4

import Definitions.Def_O3_Foundation
import Definitions.Def_O3_AboveTwo
import Theorems.Thm_O3_aboveAccumulatedWeight_zero
import Theorems.Thm_O3_aboveLevel_zero
import Theorems.Thm_O3_abovePhaseTrace_length
import Theorems.Thm_O3_lpNorm_neg
import Theorems.Thm_O3_lpNorm_zero
import Theorems.Thm_O3_lpPower_neg
import Theorems.Thm_O3_lpPower_zero
import Theorems.Thm_O3_pairing_neg_left
import Theorems.Thm_O3_pairing_neg_right
attribute [local simp] O3.lpNorm_neg
attribute [local simp] O3.lpNorm_zero
attribute [local simp] O3.lpPower_neg
attribute [local simp] O3.lpPower_zero
attribute [local simp] O3.pairing_neg_left
attribute [local simp] O3.pairing_neg_right


attribute [local simp] O3.aboveAccumulatedWeight_zero
attribute [local simp] O3.aboveLevel_zero
attribute [local simp] O3.abovePhaseTrace_length

set_option autoImplicit true
open scoped BigOperators
open O3
namespace O3
theorem _root_.solution {d S : ℕ} (oracle : PairOracle d)
    (horizons : Fin S → ℕ)
    (y accelerated : ∀ s, Fin (horizons s) → Vec d) :
    (aboveRestartTrace oracle horizons y accelerated).length =
      ((List.finRange S).map fun s => 2 * horizons s).sum := by
  simp [aboveRestartTrace, abovePhaseTrace, Nat.mul_comm]
end O3
