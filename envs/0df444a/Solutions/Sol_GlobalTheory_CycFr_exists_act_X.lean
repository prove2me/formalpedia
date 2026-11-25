-- Prove2me | solution 1 for GlobalTheory.CycFr.exists_act_X
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:38:14.79131+00:00
-- url     : https://prove2.me/submissions/c502a32d-e880-41a0-aeda-b4e8d4c8df98

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_OneAddXMulDerivativeBin
import Theorems.Thm_GlobalTheory_CycFr_constantCoeff_act
import Theorems.Thm_GlobalTheory_CycFr_coeff_one_act_X

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
theorem _root_.solution (c : ℤ_[l]) :
    ∃ v : O⟦X⟧, _root_.GlobalTheory.CycFr.act O c X = X * v ∧ constantCoeff v = algebraMap ℤ_[l] O c := by
  refine ⟨mk fun p => coeff (p + 1) (_root_.GlobalTheory.CycFr.act O c X), ?_, ?_⟩
  · have h := sub_const_eq_X_mul_shift (_root_.GlobalTheory.CycFr.act O c X)
    rwa [_root_.GlobalTheory.CycFr.constantCoeff_act, constantCoeff_X, map_zero,
      sub_zero] at h
  · rw [← coeff_zero_eq_constantCoeff_apply, coeff_mk, zero_add,
      _root_.GlobalTheory.CycFr.coeff_one_act_X]
end _root_.GlobalTheory.CycFr
end GlobalTheory.CycFr
