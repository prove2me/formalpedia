-- Prove2me | solution 1 for GlobalTheory.dvd_of_smul_apply_eq_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T04:37:18.627426+00:00
-- url     : https://prove2.me/submissions/5965910c-87b8-4fea-8b41-f3ac1aa7bef3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_GroupLikeIntegralOfFiniteFree

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution (O C A : Type) [CommRing O] [IsDomain O] [Field C] [Algebra O C]
    [IsFractionRing O C] [IsIntegrallyClosed O] [AddCommGroup A] [Module O A] [Module.Finite O A]
    (T : Module.End O A) (ε : A →ₗ[O] O) (d c : O) (a : A) (hd : d ≠ 0) (hε : ε a ≠ 0)
    (h : d • T a = c • a) : d ∣ c := by
  have hinj : Function.Injective (algebraMap O C) := IsFractionRing.injective O C
  have hd' : algebraMap O C d ≠ 0 := fun h0 => hd (hinj (by simpa using h0))
  have hε' : algebraMap O C (ε a) ≠ 0 := fun h0 => hε (hinj (by simpa using h0))
  set x : C := algebraMap O C c / algebraMap O C d with hx
  have hpow : ∀ n : ℕ, d ^ n • (T ^ n) a = c ^ n • a := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ' T, Module.End.mul_apply, pow_succ' d, mul_smul, ← map_smul T, ih, map_smul,
        smul_comm, h, ← mul_smul, ← pow_succ]
  have hpow' : ∀ n : ℕ, algebraMap O C (ε ((T ^ n) a)) = x ^ n * algebraMap O C (ε a) := by
    intro n
    have := congrArg (fun y => algebraMap O C (ε y)) (hpow n)
    simp only [map_smul, smul_eq_mul, map_mul, map_pow] at this
    rw [hx, div_pow, div_mul_eq_mul_div, eq_div_iff (pow_ne_zero _ hd'), mul_comm, this]
  have hpoly : ∀ p : Polynomial O,
      algebraMap O C (ε ((Polynomial.aeval T p) a)) = Polynomial.aeval x p * algebraMap O C (ε a) := by
    intro p
    induction p using Polynomial.induction_on' with
    | add p q hp hq => simp only [map_add, LinearMap.add_apply, hp, hq, add_mul]
    | monomial n r =>
      rw [Polynomial.aeval_monomial, Polynomial.aeval_monomial, Module.End.mul_apply,
        Module.algebraMap_end_apply, map_smul, smul_eq_mul, map_mul, hpow', mul_assoc]
  obtain ⟨p, hp, hpT⟩ := LinearMap.exists_monic_and_aeval_eq_zero O T
  have hx0 : Polynomial.aeval x p = 0 := by
    have := hpoly p
    rw [hpT] at this
    simp only [LinearMap.zero_apply, map_zero] at this
    exact (mul_eq_zero.mp this.symm).resolve_right hε'
  have hint : IsIntegral O x := ⟨p, hp, hx0⟩
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint
  refine ⟨y, hinj ?_⟩
  rw [map_mul, hy, hx, mul_div_cancel₀ _ hd']
end GlobalTheory
