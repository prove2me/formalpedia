-- Prove2me | solution 1 for GlobalTheory.CycFr.dvd_algHom_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T02:46:12.109243+00:00
-- url     : https://prove2.me/submissions/bd5609c9-f0b5-49ea-b8ab-a755bfd9817e

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
theorem _root_.solution [IsNoetherianRing O] (f g : O⟦X⟧ →ₐ[O] O⟦X⟧) (hf : (X : O⟦X⟧) ∣ f X)
    (hg : (X : O⟦X⟧) ∣ g X) (h : O⟦X⟧) (hh : h ∣ f X - g X) (a : O⟦X⟧) : h ∣ f a - g a := by
  have hX : Ideal.span {(X : O⟦X⟧)} ≤ (⊥ : Ideal O⟦X⟧).jacobson := by
    rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_jacobson_bot]
    intro y
    rw [isUnit_iff_constantCoeff]
    simp
  have hH := IsHausdorff.of_le_jacobson (Ideal.span {(X : O⟦X⟧)}) (O⟦X⟧ ⧸ Ideal.span {h}) hX
  have key : (Submodule.Quotient.mk (f a - g a) : O⟦X⟧ ⧸ Ideal.span {h}) = 0 := by
    refine hH.haus _ fun n => ?_
    rw [SModEq.zero]
    obtain ⟨r, hr⟩ := X_pow_dvd_algHom_sub_aeval_trunc f hf a n
    obtain ⟨s, hs⟩ := X_pow_dvd_algHom_sub_aeval_trunc g hg a n
    have hp : h ∣ Polynomial.aeval (f X) (trunc n a) - Polynomial.aeval (g X) (trunc n a) := by
      rw [Polynomial.aeval_def, Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map,
        Polynomial.eval₂_eq_eval_map]
      exact hh.trans (Polynomial.sub_dvd_eval_sub _ _ _)
    obtain ⟨q, hq⟩ := hp
    have he : f a - g a = X ^ n * (r - s) + h * q := by
      rw [mul_sub, ← hr, ← hs, ← hq]
      ring
    have hm : (Submodule.Quotient.mk (f a - g a) : O⟦X⟧ ⧸ Ideal.span {h}) =
        (X ^ n * (r - s)) • Submodule.Quotient.mk 1 := by
      rw [← Submodule.Quotient.mk_smul, smul_eq_mul, mul_one, Submodule.Quotient.eq, he,
        add_sub_cancel_left]
      exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self h)
    rw [hm]
    exact Submodule.smul_mem_smul
      (Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow (Ideal.mem_span_singleton_self X) n))
      Submodule.mem_top
  rw [Submodule.Quotient.mk_eq_zero, Ideal.mem_span_singleton] at key
  exact key
end _root_.GlobalTheory.CycFr
end GlobalTheory.CycFr
