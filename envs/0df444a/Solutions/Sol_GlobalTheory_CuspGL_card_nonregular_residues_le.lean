-- Prove2me | solution 1 for GlobalTheory.CuspGL.card_nonregular_residues_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T14:04:05.237495+00:00
-- url     : https://prove2.me/submissions/cde96359-50bf-4bb3-acd0-89638cd1ba56

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_AbByPOfComm
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_CardNonregularResiduesModPowSubOneLe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI
open GlobalTheory GlobalTheory.CuspGL
namespace GlobalTheory.CuspGL
theorem _root_.solution (q n : ℕ) (hq : 2 ≤ q) (hn : 0 < n) :
    ((Finset.Ioo 0 (q ^ n - 1)).filter
      (fun j => ∃ e ∈ Finset.Ioo 0 n, j * q ^ e ≡ j [MOD q ^ n - 1])).card ≤
      ∑ p ∈ n.primeFactors, (q ^ (n / p) - 2) := by
  classical
  have hsub : ((Finset.Ioo 0 (q ^ n - 1)).filter
      (fun j => ∃ e ∈ Finset.Ioo 0 n, j * q ^ e ≡ j [MOD q ^ n - 1])) ⊆
      n.primeFactors.biUnion (fun p => (Finset.Ioo 0 (q ^ (n / p) - 1)).image
        (fun k => k * ((q ^ n - 1) / (q ^ (n / p) - 1)))) := by
    intro j hj
    rw [Finset.mem_filter, Finset.mem_Ioo] at hj
    obtain ⟨⟨hj0, hjN⟩, e, he, hje⟩ := hj
    rw [Finset.mem_Ioo] at he
    have hqe : 1 ≤ q ^ e := Nat.one_le_pow _ _ (by omega)
    have h1 : q ^ n - 1 ∣ j * (q ^ e - 1) := by
      rw [Nat.mul_sub_one]
      exact (Nat.modEq_iff_dvd' (Nat.le_mul_of_pos_right j hqe)).1 hje.symm
    have h2 : q ^ n - 1 ∣ j * (q ^ Nat.gcd e n - 1) := by
      rw [← Nat.pow_sub_one_gcd_pow_sub_one, ← Nat.gcd_mul_left]
      exact Nat.dvd_gcd h1 (Dvd.intro_left j rfl)
    obtain ⟨m, hm⟩ := Nat.gcd_dvd_right e n
    have hglt : Nat.gcd e n < n := lt_of_le_of_lt (Nat.gcd_le_left n he.1) he.2
    have hm1 : m ≠ 1 := by
      rintro rfl
      omega
    obtain ⟨p, hp, r, hr⟩ := Nat.exists_prime_and_dvd hm1
    have hnp : n = p * (Nat.gcd e n * r) := by
      conv_lhs => rw [hm, hr]
      ring
    have hd : n / p = Nat.gcd e n * r := Nat.div_eq_of_eq_mul_right hp.pos hnp
    have hpn : p ∣ n := ⟨_, hnp⟩
    have hd0 : n / p ≠ 0 := (Nat.div_pos (Nat.le_of_dvd hn hpn) hp.pos).ne'
    have h3 : q ^ n - 1 ∣ j * (q ^ (n / p) - 1) :=
      h2.trans (Nat.mul_dvd_mul_left j
        (Nat.pow_sub_one_dvd_pow_sub_one q ⟨r, hd⟩))
    have h4 : q ^ (n / p) - 1 ∣ q ^ n - 1 :=
      Nat.pow_sub_one_dvd_pow_sub_one q (Nat.div_dvd_of_dvd hpn)
    have hD : 0 < q ^ (n / p) - 1 := by
      have := Nat.one_lt_pow hd0 (show 1 < q by omega)
      omega
    obtain ⟨M, hM⟩ := h4
    rw [Finset.mem_biUnion]
    refine ⟨p, Nat.mem_primeFactors.2 ⟨hp, hpn, hn.ne'⟩, ?_⟩
    rw [hM, mul_comm j] at h3
    obtain ⟨k, hk⟩ := Nat.dvd_of_mul_dvd_mul_left hD h3
    rw [Finset.mem_image]
    refine ⟨k, Finset.mem_Ioo.2 ⟨?_, ?_⟩, ?_⟩
    · rcases Nat.eq_zero_or_pos k with rfl | h
      · omega
      · exact h
    · rw [hM, hk, mul_comm _ M] at hjN
      exact lt_of_mul_lt_mul_left hjN (Nat.zero_le _)
    · rw [hM, Nat.mul_div_cancel_left _ hD, hk, mul_comm]
  refine (Finset.card_le_card hsub).trans (Finset.card_biUnion_le.trans ?_)
  refine Finset.sum_le_sum fun p _ => Finset.card_image_le.trans ?_
  rw [Nat.card_Ioo]
  omega
end GlobalTheory.CuspGL
