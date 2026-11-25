-- Prove2me | solution 1 for GlobalTheory.CycFr.act_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:38:04.289662+00:00
-- url     : https://prove2.me/submissions/d15b5d73-8083-4afa-ae23-a4101662c3ed

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_OneAddXMulDerivativeBin
import Theorems.Thm_GlobalTheory_CycFr_algHom_ext_X
import Theorems.Thm_GlobalTheory_CycFr_act_X
import Theorems.Thm_GlobalTheory_CycFr_X_dvd_act_X
import Theorems.Thm_GlobalTheory_CycFr_bin_one

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
omit [IsDomain O] [CharZero O]
namespace GlobalTheory.CycFr
namespace _root_.GlobalTheory.CycFr
theorem _root_.solution (a : O⟦X⟧) : _root_.GlobalTheory.CycFr.act O (1 : ℤ_[l]) a = a := by
  have h : _root_.GlobalTheory.CycFr.act O (1 : ℤ_[l]) = AlgHom.id O O⟦X⟧ :=
    _root_.GlobalTheory.CycFr.algHom_ext_X _ _ (_root_.GlobalTheory.CycFr.X_dvd_act_X 1)
      (by rw [_root_.GlobalTheory.CycFr.act_X, _root_.GlobalTheory.CycFr.bin_one,
        add_sub_cancel_left, AlgHom.id_apply])
  rw [h, AlgHom.id_apply]
end _root_.GlobalTheory.CycFr
end GlobalTheory.CycFr
