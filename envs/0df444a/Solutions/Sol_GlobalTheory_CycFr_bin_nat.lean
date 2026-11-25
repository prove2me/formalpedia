-- Prove2me | solution 1 for GlobalTheory.CycFr.bin_nat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T02:04:51.994801+00:00
-- url     : https://prove2.me/submissions/c6f03c97-15ad-4f15-b77d-30237ce00693

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_OneAddXMulDerivativeBin

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
theorem _root_.solution (d : ℕ) : _root_.GlobalTheory.CycFr.bin O (d : ℤ_[l]) = (1 + X) ^ d :=
  binomialSeries_nat d
end _root_.GlobalTheory.CycFr
end GlobalTheory.CycFr
