-- Prove2me | solution 1 for GlobalTheory.CycFr.act_one_add_X
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T02:28:45.267105+00:00
-- url     : https://prove2.me/submissions/7b351639-0536-4044-a764-c560d4e0545c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_OneAddXMulDerivativeBin
import Theorems.Thm_GlobalTheory_CycFr_act_X

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PowerSeries
open GlobalTheory GlobalTheory.CycFr
variable {l : ℕ} [Fact l.Prime] (O : Type) [CommRing O] [Algebra ℤ_[l] O]
variable {O}
open PowerSeries
variable {l : ℕ} [Fact l.Prime] (O : Type) [CommRing O] [Algebra ℤ_[l] O]
variable {O}
namespace GlobalTheory.CycFr
namespace _root_.GlobalTheory.CycFr
theorem _root_.solution (c : ℤ_[l]) : _root_.GlobalTheory.CycFr.act O c (1 + X) = _root_.GlobalTheory.CycFr.bin O c := by
  rw [map_add, map_one, _root_.GlobalTheory.CycFr.act_X]
  ring
end _root_.GlobalTheory.CycFr
end GlobalTheory.CycFr
