-- Prove2me | solution 1 for GlobalTheory.TupleCone.mem_saturation_of_isIntegral
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T13:03:29.156651+00:00
-- url     : https://prove2.me/submissions/36c92ef6-6d43-483e-9594-fd276cbf1e71

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_FiniteIntegralClosureOfEssFiniteTypeField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsIntegralRatioRingIffMemAdjoin

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.TupleCone
open Polynomial
variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
namespace GlobalTheory.TupleCone
theorem _root_.solution {x : B} (hx : IsIntegral A x) {b : B}
    (hb : IsIntegral (saturation x hx) b) : b ∈ saturation x hx := by
  rcases subsingleton_or_nontrivial B with hB | hB
  · rw [Subsingleton.elim b 0]
    exact zero_mem _
  obtain ⟨p, hp, hz⟩ := hb
  have hr : ∀ r : saturation x hx, ∃ n : ℕ, IsIntegral A ((r : B) * x ^ n) := fun r => r.2
  choose n hn using hr
  let N := p.support.sup fun i => n (p.coeff i)
  have hN : ∀ i k, k ≠ 0 → IsIntegral A ((p.coeff i : B) * (x ^ N) ^ k) := by
    intro i k hk
    by_cases hi : i ∈ p.support
    · have h1 : n (p.coeff i) ≤ N * k :=
        (Finset.le_sup (f := fun i => n (p.coeff i)) hi).trans
          (Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero hk))
      obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le h1
      rw [← pow_mul, hd, pow_add, ← mul_assoc]
      exact (hn _).mul (hx.pow _)
    · rw [notMem_support_iff.mp hi, ZeroMemClass.coe_zero, zero_mul]
      exact isIntegral_zero
  let q := p.map (algebraMap (saturation x hx) B)
  have hq : q.Monic := hp.map _
  have hqz : q.eval b = 0 := by rw [eval_map, hz]
  have hq0 : q.natDegree ≠ 0 := by
    intro h
    rw [hq.natDegree_eq_zero.mp h] at hqz
    simp at hqz
  refine ⟨N, IsIntegral.of_aeval_monic_of_isIntegral_coeff (p := q.scaleRoots (x ^ N))
    ((monic_scaleRoots_iff _).mpr hq) (by rwa [natDegree_scaleRoots]) ?_ fun i => ?_⟩
  · rw [mul_comm, scaleRoots_eval_mul, hqz, mul_zero]
    exact isIntegral_zero
  · rw [coeff_scaleRoots]
    rcases lt_trichotomy i q.natDegree with h | rfl | h
    · rw [coeff_map]
      exact hN _ _ (by omega)
    · simpa [hq.coeff_natDegree] using isIntegral_one
    · simpa [coeff_eq_zero_of_natDegree_lt h] using isIntegral_zero
end GlobalTheory.TupleCone
