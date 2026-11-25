-- Prove2me | solution 1 for GlobalTheory.CycFr.act_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T02:05:10.658849+00:00
-- url     : https://prove2.me/submissions/7a36307a-9d36-48c7-8ce6-e1563091dfb0

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
theorem _root_.solution (c : ℤ_[l]) (a : O⟦X⟧) : _root_.GlobalTheory.CycFr.act O c a = a.subst (_root_.GlobalTheory.CycFr.bin O c - 1) := by
  rw [_root_.GlobalTheory.CycFr.act, coe_substAlgHom]
end _root_.GlobalTheory.CycFr
end GlobalTheory.CycFr
