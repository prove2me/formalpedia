-- Prove2me | solution 1 for GlobalTheory.CycFr.bin_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T02:20:16.870746+00:00
-- url     : https://prove2.me/submissions/435154ed-c5ad-486f-a3ca-a9ff90b0abcc

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_OneAddXMulDerivativeBin
import Theorems.Thm_GlobalTheory_CycFr_bin_nat

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
theorem _root_.solution : _root_.GlobalTheory.CycFr.bin O (1 : ℤ_[l]) = 1 + X := by
  have h := _root_.GlobalTheory.CycFr.bin_nat (O := O) (l := l) 1
  rwa [Nat.cast_one, pow_one] at h
end _root_.GlobalTheory.CycFr
end GlobalTheory.CycFr
