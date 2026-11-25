-- Prove2me | solution 1 for GlobalTheory.CycFr.algHom_ext_X
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T02:07:23.367381+00:00
-- url     : https://prove2.me/submissions/f2da4eef-e630-4a94-8eb3-336fa3f43886

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_OneAddXMulDerivativeBin
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
open PowerSeries in
private theorem algHom_coe_polynomial_eq_aeval {O : Type} [CommRing O] (f : O⟦X⟧ →ₐ[O] O⟦X⟧)
    (p : Polynomial O) : f (p : O⟦X⟧) = Polynomial.aeval (f X) p := by
  have hfp : f.comp (Polynomial.coeToPowerSeries.algHom O) = Polynomial.aeval (f X) :=
    Polynomial.algHom_ext (by simp)
  have := DFunLike.congr_fun hfp p
  simpa using this
open PowerSeries in
private theorem X_pow_dvd_algHom_sub_aeval_trunc {O : Type} [CommRing O] (f : O⟦X⟧ →ₐ[O] O⟦X⟧)
    (hf : (X : O⟦X⟧) ∣ f X) (a : O⟦X⟧) (n : ℕ) :
    (X : O⟦X⟧) ^ n ∣ f a - Polynomial.aeval (f X) (trunc n a) := by
  obtain ⟨s, hs⟩ : ∃ s : O⟦X⟧, a = X ^ n * s + (trunc n a : O⟦X⟧) := ⟨_, eq_X_pow_mul_shift_add_trunc n a⟩
  rw [← algHom_coe_polynomial_eq_aeval]
  have hdiff : f a - f ↑(trunc n a) = f X ^ n * f s := by
    calc f a - f ↑(trunc n a) = f (X ^ n * s + ↑(trunc n a)) - f ↑(trunc n a) := by rw [← hs]
      _ = f X ^ n * f s := by rw [map_add, map_mul, map_pow, add_sub_cancel_right]
  rw [hdiff]
  exact Dvd.dvd.mul_right (pow_dvd_pow_of_dvd hf n) _
variable {l : ℕ} [Fact l.Prime] (O : Type) [CommRing O] [Algebra ℤ_[l] O]
variable {O}
variable [IsDomain O] [CharZero O]
end GlobalTheory.CycFr
end
end

set_option autoImplicit false
noncomputable section
open PowerSeries
open GlobalTheory GlobalTheory.CycFr
open PowerSeries
namespace GlobalTheory.CycFr
namespace _root_.GlobalTheory.CycFr
theorem _root_.solution {O : Type} [CommRing O] (f g : O⟦X⟧ →ₐ[O] O⟦X⟧)
    (hf : (X : O⟦X⟧) ∣ f X) (h : f X = g X) : f = g := by
  ext a : 1
  refine PowerSeries.ext fun n => ?_
  have h1 := X_pow_dvd_algHom_sub_aeval_trunc f hf a (n + 1)
  have h2 := X_pow_dvd_algHom_sub_aeval_trunc g (h ▸ hf) a (n + 1)
  rw [← h] at h2
  have h3 := dvd_sub h1 h2
  rw [sub_sub_sub_cancel_right] at h3
  have := X_pow_dvd_iff.mp h3 n (Nat.lt_succ_self n)
  rwa [map_sub, sub_eq_zero] at this
end _root_.GlobalTheory.CycFr
end GlobalTheory.CycFr
