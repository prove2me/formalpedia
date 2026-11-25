-- Prove2me | solution 1 for GlobalTheory.CycFr.act_bin
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T03:36:15.459096+00:00
-- url     : https://prove2.me/submissions/d630e4e4-5af0-482b-830d-51318cfac77e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_OneAddXMulDerivativeBin
import Theorems.Thm_GlobalTheory_CycFr_act_apply
import Theorems.Thm_GlobalTheory_CycFr_act_one_add_X
import Theorems.Thm_GlobalTheory_CycFr_act_C
import Theorems.Thm_GlobalTheory_CycFr_constantCoeff_act
import Theorems.Thm_GlobalTheory_CycFr_bin_one
import Theorems.Thm_GlobalTheory_CycFr_derivative_bin
import Theorems.Thm_GlobalTheory_CycFr_one_add_X_mul_derivative_bin
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
open PowerSeries in
variable {l : ℕ} [Fact l.Prime] (O : Type) [CommRing O] [Algebra ℤ_[l] O] in
variable {O} in
variable [IsDomain O] [CharZero O] in
private theorem eq_of_one_add_X_mul_derivative_eq_C_mul {F H : O⟦X⟧} (a : O)
    (hF : (1 + X) * derivative O F = C a * F) (hH : (1 + X) * derivative O H = C a * H)
    (h0 : constantCoeff F = constantCoeff H) : F = H := by
  have hD : (1 + X) * derivative O (F - H) = C a * (F - H) := by
    rw [map_sub, mul_sub, mul_sub, hF, hH]
  have hD0 : coeff 0 (F - H) = 0 := by
    rw [coeff_zero_eq_constantCoeff_apply, map_sub, h0, sub_self]
  have key : ∀ n, coeff n (F - H) = 0 ∧ coeff n (derivative O (F - H)) = 0 := by
    intro n
    induction n with
    | zero =>
      refine ⟨hD0, ?_⟩
      have h := congrArg (coeff 0) hD
      rwa [add_mul, one_mul, map_add, coeff_zero_X_mul, add_zero, coeff_C_mul, hD0,
        mul_zero] at h
    | succ m ih =>
      have h1 : coeff (m + 1) (F - H) = 0 := by
        have h := ih.2
        rw [coeff_derivative] at h
        exact (mul_eq_zero.mp h).resolve_right (Nat.cast_add_one_ne_zero m)
      refine ⟨h1, ?_⟩
      have h := congrArg (coeff (m + 1)) hD
      rwa [add_mul, one_mul, map_add, coeff_succ_X_mul, ih.2, add_zero, coeff_C_mul, h1,
        mul_zero] at h
  ext n
  have h := (key n).1
  rwa [map_sub, sub_eq_zero] at h
end GlobalTheory.CycFr
end
end

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
theorem _root_.solution (c d : ℤ_[l]) :
    _root_.GlobalTheory.CycFr.act O c (_root_.GlobalTheory.CycFr.bin O d) =
      _root_.GlobalTheory.CycFr.bin O (c * d) := by
  have hG : derivative O (_root_.GlobalTheory.CycFr.act O c (_root_.GlobalTheory.CycFr.bin O d)) =
      _root_.GlobalTheory.CycFr.act O c (derivative O (_root_.GlobalTheory.CycFr.bin O d)) *
        derivative O (_root_.GlobalTheory.CycFr.bin O c) := by
    rw [_root_.GlobalTheory.CycFr.act_apply, _root_.GlobalTheory.CycFr.act_apply,
      derivative_subst (_root_.GlobalTheory.CycFr.hasSubst_bin O c), map_sub,
      Derivation.map_one_eq_zero, sub_zero]
  have h1 : _root_.GlobalTheory.CycFr.act O c (_root_.GlobalTheory.CycFr.bin O d) =
      _root_.GlobalTheory.CycFr.act O c (_root_.GlobalTheory.CycFr.bin O (d - 1)) *
        _root_.GlobalTheory.CycFr.bin O c := by
    rw [← one_add_X_mul_bin_sub_one_eq_bin d, map_mul,
      _root_.GlobalTheory.CycFr.act_one_add_X, mul_comm]
  refine eq_of_one_add_X_mul_derivative_eq_C_mul (algebraMap ℤ_[l] O (c * d)) ?_
    (_root_.GlobalTheory.CycFr.one_add_X_mul_derivative_bin (c * d)) ?_
  · rw [hG, _root_.GlobalTheory.CycFr.derivative_bin, _root_.GlobalTheory.CycFr.derivative_bin, h1,
      ← one_add_X_mul_bin_sub_one_eq_bin c]
    simp only [map_mul, _root_.GlobalTheory.CycFr.act_C]
    ring
  · rw [_root_.GlobalTheory.CycFr.constantCoeff_act, binomialSeries_constantCoeff,
      binomialSeries_constantCoeff]
end _root_.GlobalTheory.CycFr
end GlobalTheory.CycFr
