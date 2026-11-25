-- Prove2me | solution 1 for GlobalTheory.CycFr.one_add_X_mul_derivative_bin
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T02:59:33.988655+00:00
-- url     : https://prove2.me/submissions/409a2d8f-3de9-48cb-8229-4481373c818d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_OneAddXMulDerivativeBin
import Theorems.Thm_GlobalTheory_CycFr_bin_one
import Theorems.Thm_GlobalTheory_CycFr_derivative_bin
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open PowerSeries
namespace GlobalTheory.CycFr
variable {l : ℕ} [Fact l.Prime] (O : Type) [CommRing O] [Algebra ℤ_[l] O]
variable {O}
open PowerSeries in
variable {l : ℕ} [Fact l.Prime] (O : Type) [CommRing O] [Algebra ℤ_[l] O] in
variable {O} in
private theorem one_add_X_mul_bin_sub_one_eq_bin (c : ℤ_[l]) :
    (1 + X : O⟦X⟧) * _root_.GlobalTheory.CycFr.bin O (c - 1) = _root_.GlobalTheory.CycFr.bin O c := by
  have h : _root_.GlobalTheory.CycFr.bin O c =
      _root_.GlobalTheory.CycFr.bin O (c - 1) * _root_.GlobalTheory.CycFr.bin O (1 : ℤ_[l]) := by
    simp only [_root_.GlobalTheory.CycFr.bin, ← binomialSeries_add, sub_add_cancel]
  rw [h, _root_.GlobalTheory.CycFr.bin_one, mul_comm]
variable [IsDomain O] [CharZero O]
end GlobalTheory.CycFr
end
end

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
theorem _root_.solution (c : ℤ_[l]) :
    (1 + X : O⟦X⟧) * derivative O (_root_.GlobalTheory.CycFr.bin O c) =
      C (algebraMap ℤ_[l] O c) * _root_.GlobalTheory.CycFr.bin O c := by
  rw [_root_.GlobalTheory.CycFr.derivative_bin, mul_left_comm,
    one_add_X_mul_bin_sub_one_eq_bin]
end _root_.GlobalTheory.CycFr
end GlobalTheory.CycFr
