-- Prove2me | solution 1 for GlobalTheory.CycFr.dvd_sub_C_of_shift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:38:11.68619+00:00
-- url     : https://prove2.me/submissions/d0b7bc2f-20bf-4610-981e-c6af9fbc9ef3

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
variable [IsDomain O] [CharZero O]
open PowerSeries
variable {l : ℕ} [Fact l.Prime] (O : Type) [CommRing O] [Algebra ℤ_[l] O]
variable {O}
variable [IsDomain O] [CharZero O]
omit [Fact l.Prime] [Algebra ℤ_[l] O] [IsDomain O] [CharZero O]
namespace GlobalTheory.CycFr
namespace _root_.GlobalTheory.CycFr
theorem _root_.solution (x : O) (σ : O⟦X⟧ ≃ₐ[O] O⟦X⟧) (hσ : σ X = X + C x) (a : O⟦X⟧) :
    X - C x ∣ a - C (constantCoeff (σ a)) := by
  have hC : ∀ y : O, (C y : O⟦X⟧) = algebraMap O O⟦X⟧ y := fun y => by simp
  have hinv : σ.symm X = X - C x := by
    apply σ.injective
    rw [AlgEquiv.apply_symm_apply, map_sub, hσ, hC, AlgEquiv.commutes]
    ring
  have hs := congrArg σ.symm (sub_const_eq_X_mul_shift (σ a))
  rw [map_sub, map_mul, AlgEquiv.symm_apply_apply, hinv, hC, AlgEquiv.commutes, ← hC] at hs
  exact ⟨_, hs⟩
end _root_.GlobalTheory.CycFr
end GlobalTheory.CycFr
