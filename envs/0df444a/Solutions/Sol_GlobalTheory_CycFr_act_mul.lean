-- Prove2me | solution 1 for GlobalTheory.CycFr.act_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T04:13:56.019013+00:00
-- url     : https://prove2.me/submissions/573b0c1c-7dfd-4b42-9ba2-f6a6acd9ddd5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_OneAddXMulDerivativeBin
import Theorems.Thm_GlobalTheory_CycFr_act_apply
import Theorems.Thm_GlobalTheory_CycFr_act_bin

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
variable [IsDomain O] [CharZero O]
open PowerSeries
variable {l : ℕ} [Fact l.Prime] (O : Type) [CommRing O] [Algebra ℤ_[l] O]
variable {O}
variable [IsDomain O] [CharZero O]
namespace GlobalTheory.CycFr
namespace _root_.GlobalTheory.CycFr
theorem _root_.solution (c d : ℤ_[l]) (a : O⟦X⟧) : _root_.GlobalTheory.CycFr.act O (c * d) a = _root_.GlobalTheory.CycFr.act O c (_root_.GlobalTheory.CycFr.act O d a) := by
  rw [_root_.GlobalTheory.CycFr.act_apply, _root_.GlobalTheory.CycFr.act_apply,
    _root_.GlobalTheory.CycFr.act_apply,
    subst_comp_subst_apply (_root_.GlobalTheory.CycFr.hasSubst_bin O d)
      (_root_.GlobalTheory.CycFr.hasSubst_bin O c)]
  congr 1
  rw [← _root_.GlobalTheory.CycFr.act_apply, map_sub, map_one,
    _root_.GlobalTheory.CycFr.act_bin]
end _root_.GlobalTheory.CycFr
end GlobalTheory.CycFr
