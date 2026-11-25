-- Prove2me | solution 1 for GlobalTheory.exists_isIntegral_mul_pow_of_subalgebra
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T13:05:22.721427+00:00
-- url     : https://prove2.me/submissions/5e24675f-3f35-4098-99ce-c4d9d344b842

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_FiniteIntegralClosureOfEssFiniteTypeField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsIsIntegralMulPowOfSubalgebra

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open Polynomial
variable {o Ω : Type*} [CommRing o] [Field Ω] [Algebra o Ω] {J : Type*}
namespace GlobalTheory
theorem _root_.solution (A B : Subalgebra o Ω) {u : Ω} (hu : u ∈ B)
    (hr : ∀ r ∈ A, ∃ n : ℕ, r * u ^ n ∈ B) {z : Ω} (hz : IsIntegral A z) :
    ∃ N : ℕ, ∀ M, N ≤ M → IsIntegral B (z * u ^ M) := by
  have hB : ∀ x ∈ B, IsIntegral B x := fun x hx => isIntegral_algebraMap (x := (⟨x, hx⟩ : B))
  suffices ∃ N : ℕ, IsIntegral B (z * u ^ N) by
    obtain ⟨N, hN⟩ := this
    refine ⟨N, fun M hM => ?_⟩
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hM
    rw [pow_add, ← mul_assoc]
    exact hN.mul (hB _ (pow_mem hu _))
  obtain ⟨p, hp, hz⟩ := hz
  choose n hn using fun r : A => hr r r.2
  let N := p.support.sup fun i => n (p.coeff i)
  have hN : ∀ i k, k ≠ 0 → IsIntegral B (algebraMap A Ω (p.coeff i) * (u ^ N) ^ k) := by
    intro i k hk
    by_cases hi : i ∈ p.support
    · have h1 : n (p.coeff i) ≤ N * k :=
        (Finset.le_sup (f := fun i => n (p.coeff i)) hi).trans
          (Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero hk))
      obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le h1
      rw [← pow_mul, hd, pow_add, ← mul_assoc]
      exact hB _ (mul_mem (hn _) (pow_mem hu _))
    · rw [notMem_support_iff.mp hi, map_zero, zero_mul]
      exact isIntegral_zero
  let q := p.map (algebraMap A Ω)
  have hq : q.Monic := hp.map _
  have hqz : q.eval z = 0 := by rw [eval_map, hz]
  have hq0 : q.natDegree ≠ 0 := by
    intro h
    rw [hq.natDegree_eq_zero.mp h] at hqz
    simp at hqz
  refine ⟨N, IsIntegral.of_aeval_monic_of_isIntegral_coeff (p := q.scaleRoots (u ^ N))
    ((monic_scaleRoots_iff _).mpr hq) (by rwa [natDegree_scaleRoots]) ?_ fun i => ?_⟩
  · rw [mul_comm, scaleRoots_eval_mul, hqz, mul_zero]
    exact isIntegral_zero
  · rw [coeff_scaleRoots]
    rcases lt_trichotomy i q.natDegree with h | rfl | h
    · rw [coeff_map]
      exact hN _ _ (by omega)
    · simpa [hq.coeff_natDegree] using isIntegral_one
    · simpa [coeff_eq_zero_of_natDegree_lt h] using isIntegral_zero
end GlobalTheory
