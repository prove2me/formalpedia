-- Prove2me | solution 1 for O3.abovePhaseTrace_length
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:05:10.915721+00:00
-- url     : https://prove2.me/submissions/3a043974-774b-4688-af57-5a87ff297355

import Definitions.Def_O3_Foundation
import Definitions.Def_O3_AboveTwo
import Theorems.Thm_O3_aboveAccumulatedWeight_zero
import Theorems.Thm_O3_aboveLevel_zero
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

set_option autoImplicit true
open scoped BigOperators
open O3
namespace O3
theorem _root_.solution {d N : ℕ} (oracle : PairOracle d)
    (y accelerated : Fin N → Vec d) :
    (abovePhaseTrace oracle y accelerated).length = 2 * N := by
  simp [abovePhaseTrace]
  omega
end O3
