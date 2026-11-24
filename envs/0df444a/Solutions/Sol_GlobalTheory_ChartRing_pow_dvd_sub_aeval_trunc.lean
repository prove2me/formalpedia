-- Prove2me | solution 1 for GlobalTheory.ChartRing.pow_dvd_sub_aeval_trunc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T12:10:45.418684+00:00
-- url     : https://prove2.me/submissions/44435662-ca46-4846-89d8-423ac3e2dbc0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsAdicCompleteComapConstantCoeff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PowerSeries
noncomputable section
open GlobalTheory GlobalTheory.ChartRing
variable {A S : Type*} [CommRing A] [CommRing S] [Algebra A S]
namespace GlobalTheory.ChartRing
theorem _root_.solution (φ : A⟦X⟧ →ₐ[A] S) (n : ℕ) (f : A⟦X⟧) :
    φ X ^ n ∣ φ f - Polynomial.aeval (φ X) (trunc n f) := by
  have h1 : ∀ p : Polynomial A, φ (p : A⟦X⟧) = Polynomial.aeval (φ X) p := by
    intro p
    have : φ.comp (Polynomial.coeToPowerSeries.algHom A) = Polynomial.aeval (φ X) := by
      ext; simp
    simpa using DFunLike.congr_fun this p
  refine ⟨φ (mk fun i => coeff (i + n) f), ?_⟩
  conv_lhs => rw [f.eq_X_pow_mul_shift_add_trunc n]
  rw [← h1, ← map_pow, ← map_mul, ← map_sub]
  congr 1
  rw [← f.eq_X_pow_mul_shift_add_trunc n, sub_eq_iff_eq_add]
  exact f.eq_X_pow_mul_shift_add_trunc n
end GlobalTheory.ChartRing
