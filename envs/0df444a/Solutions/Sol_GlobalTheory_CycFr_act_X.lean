-- Prove2me | solution 1 for GlobalTheory.CycFr.act_X
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T02:15:20.196795+00:00
-- url     : https://prove2.me/submissions/4c568439-b969-40df-b42c-97fd777fc9bd

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_OneAddXMulDerivativeBin
import Theorems.Thm_GlobalTheory_CycFr_act_apply

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
theorem _root_.solution (c : ℤ_[l]) : _root_.GlobalTheory.CycFr.act O c X = _root_.GlobalTheory.CycFr.bin O c - 1 := by
  rw [_root_.GlobalTheory.CycFr.act_apply, subst_X (_root_.GlobalTheory.CycFr.hasSubst_bin O c)]
end _root_.GlobalTheory.CycFr
end GlobalTheory.CycFr
