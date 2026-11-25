-- Prove2me | solution 1 for GlobalTheory.CycFr.dvd_act_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:38:08.139373+00:00
-- url     : https://prove2.me/submissions/913d3fbd-b321-4129-9c12-a455006bd759

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_OneAddXMulDerivativeBin
import Theorems.Thm_GlobalTheory_CycFr_act_X
import Theorems.Thm_GlobalTheory_CycFr_X_dvd_act_X
import Theorems.Thm_GlobalTheory_CycFr_dvd_bin_sub
import Theorems.Thm_GlobalTheory_CycFr_dvd_algHom_sub

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
theorem _root_.solution [IsNoetherianRing O] (k : ℕ) (c d : ℤ_[l]) (h : (l : ℤ_[l]) ^ k ∣ c - d)
    (a : O⟦X⟧) : (1 + X : O⟦X⟧) ^ l ^ k - 1 ∣ _root_.GlobalTheory.CycFr.act O c a - _root_.GlobalTheory.CycFr.act O d a := by
  refine _root_.GlobalTheory.CycFr.dvd_algHom_sub _ _ (_root_.GlobalTheory.CycFr.X_dvd_act_X c)
    (_root_.GlobalTheory.CycFr.X_dvd_act_X d) _ ?_ a
  rw [_root_.GlobalTheory.CycFr.act_X, _root_.GlobalTheory.CycFr.act_X,
    sub_sub_sub_cancel_right]
  exact _root_.GlobalTheory.CycFr.dvd_bin_sub k c d h
end _root_.GlobalTheory.CycFr
end GlobalTheory.CycFr
