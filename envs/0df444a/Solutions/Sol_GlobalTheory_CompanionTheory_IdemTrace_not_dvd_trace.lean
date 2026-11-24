-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.IdemTrace.not_dvd_trace
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T12:55:17.20787+00:00
-- url     : https://prove2.me/submissions/128c5643-3c80-4fb9-a06d-7d305dfc1a02

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_TraceIdempotentNotDivisible
import Theorems.Thm_GlobalTheory_CompanionTheory_IdemTrace_exists_nat_trace_of_idem
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace GlobalTheory.CompanionTheory.IdemTrace
private lemma isLocalRing_zmod_prime_pow (p m : ℕ) [hp : Fact p.Prime] (hm : 0 < m) :
    IsLocalRing (ZMod (p ^ m)) := by
  have : Fact (1 < p ^ m) := ⟨Nat.one_lt_pow hm.ne' hp.out.one_lt⟩
  refine IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun a => ?_
  by_contra hcon0
  have hcon := not_or.mp hcon0
  let φ := ZMod.castHom (dvd_pow_self p hm.ne') (ZMod p)
  have key : ∀ b : ZMod (p ^ m), ¬ IsUnit b → φ b = 0 := by
    intro b hb
    rw [← ZMod.natCast_zmod_val b] at hb ⊢
    rw [ZMod.isUnit_iff_coprime, Nat.coprime_pow_right_iff hm, Nat.coprime_comm,
      Nat.Prime.coprime_iff_not_dvd hp.out, not_not] at hb
    rw [map_natCast, ZMod.natCast_eq_zero_iff]
    exact hb
  have h1 := congrArg φ (add_sub_cancel a 1)
  rw [map_add, key a hcon.1, key _ hcon.2, add_zero, map_one] at h1
  exact zero_ne_one h1
end GlobalTheory.CompanionTheory.IdemTrace
end

set_option autoImplicit false
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.IdemTrace
namespace GlobalTheory.CompanionTheory.IdemTrace
theorem _root_.solution : ∀ (B : Type) [CommRing B] [Module.Free ℤ B] [Module.Finite ℤ B] (x : B)
    (p m : ℕ), p.Prime → Module.finrank ℤ B < p ^ m →
    x * x - x ∈ Ideal.span {((p : B)) ^ m} → x ∉ Ideal.span {((p : B)) ^ m} →
    ¬ ((p : ℤ) ^ m ∣ Algebra.trace ℤ B x) := by
  intro B _ _ _ x p m hp hrank hidem hnot hdvd
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · apply hnot
    simp
  have : Fact p.Prime := ⟨hp⟩
  have := isLocalRing_zmod_prime_pow p m hm
  classical
  let b := Module.finBasis ℤ B
  let M := Algebra.leftMulMatrix b x
  let φ := Int.castRingHom (ZMod (p ^ m))
  let P := φ.mapMatrix M
  have hpm : (((p : ℤ) ^ m : ℤ) : ZMod (p ^ m)) = 0 := by
    push_cast
    exact_mod_cast ZMod.natCast_self (p ^ m)
  obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.mp hidem
  have hz : y * (p : B) ^ m = ((p : ℤ) ^ m) • y := by
    rw [zsmul_eq_mul, Int.cast_pow, Int.cast_natCast, mul_comm]
  have hP : P * P = P := by
    have hMM : M * M - M = ((p : ℤ) ^ m) • Algebra.leftMulMatrix b y := by
      rw [← map_zsmul, ← hz, hy, map_sub, map_mul]
    rw [← sub_eq_zero]
    show φ.mapMatrix M * φ.mapMatrix M - φ.mapMatrix M = 0
    rw [← map_mul, ← map_sub, hMM, map_zsmul, ← Int.cast_smul_eq_zsmul (ZMod (p ^ m)), hpm,
      zero_smul]
  obtain ⟨r, hr, htr, hr0⟩ := exists_nat_trace_of_idem P hP
  have htrace : ((Algebra.trace ℤ B x : ℤ) : ZMod (p ^ m)) = P.trace := by
    rw [Algebra.trace_eq_matrix_trace b x]
    simp [P, M, φ, Matrix.trace, Matrix.diag]
  obtain ⟨k, hk⟩ := hdvd
  have hr_zero : (r : ZMod (p ^ m)) = 0 := by
    rw [← htr, ← htrace, hk, Int.cast_mul, hpm, zero_mul]
  rw [ZMod.natCast_eq_zero_iff] at hr_zero
  have hr' : r = 0 := Nat.eq_zero_of_dvd_of_lt hr_zero (by omega)
  have hP0 := hr0 hr'
  have hent : ∀ i j, ((p : ℤ) ^ m) ∣ M i j := by
    intro i j
    have h1 : φ (M i j) = 0 := by
      have := congrFun (congrFun hP0 i) j
      simpa [P] using this
    have h2 := (ZMod.intCast_zmod_eq_zero_iff_dvd (M i j) (p ^ m)).mp h1
    exact_mod_cast h2
  apply hnot
  have hxb : ∀ j, x * b j ∈ Ideal.span {((p : B)) ^ m} := by
    intro j
    rw [← b.sum_repr (x * b j)]
    refine Ideal.sum_mem _ (fun i _ => ?_)
    have hM : b.repr (x * b j) i = M i j := (Algebra.leftMulMatrix_eq_repr_mul b x i j).symm
    obtain ⟨c, hc⟩ := hent i j
    rw [hM, hc, Ideal.mem_span_singleton]
    refine ⟨c • b i, ?_⟩
    rw [mul_smul, zsmul_eq_mul, Int.cast_pow, Int.cast_natCast]
  rw [← mul_one x, ← b.sum_repr 1, Finset.mul_sum]
  refine Ideal.sum_mem _ (fun j _ => ?_)
  rw [mul_smul_comm]
  exact Submodule.smul_of_tower_mem _ _ (hxb j)
end GlobalTheory.CompanionTheory.IdemTrace
