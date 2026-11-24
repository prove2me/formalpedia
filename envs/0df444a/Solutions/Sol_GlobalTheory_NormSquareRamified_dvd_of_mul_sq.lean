-- Prove2me | solution 1 for GlobalTheory.NormSquareRamified.dvd_of_mul_sq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T19:14:46.474543+00:00
-- url     : https://prove2.me/submissions/dfa527c4-461f-4f9e-b496-e502972824b9

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_DataHost
import Definitions.Def_Formalism_FrobeniusOrbits_HostCorollaries
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_IsUnitNormOfIsCoprime
import Theorems.Thm_Formalism_FrobeniusOrbits_galEquiv_apply
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.FrobeniusOrbits.galEquiv_apply
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
open NumberField IsDedekindDomain
open GlobalTheory GlobalTheory.NormSquareRamified
namespace GlobalTheory.NormSquareRamified
theorem _root_.solution {p : ℕ} (hp : p.Prime) {q D : ℤ} (hq : ¬ (p : ℤ) ∣ q) (B : ℚ)
    (h : ((q * p : ℤ) : ℚ) * B ^ 2 = D) : (p : ℤ) ∣ D := by
  have hpp : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  by_contra hD
  have hden : (B.den : ℚ) ≠ 0 := by exact_mod_cast B.den_nz
  have h1 : q * p * B.num ^ 2 = D * (B.den : ℤ) ^ 2 := by
    have hB : (B.num : ℚ) = B * B.den := by
      rw [Rat.mul_den_eq_num]
    have : ((q * p * B.num ^ 2 : ℤ) : ℚ) = ((D * (B.den : ℤ) ^ 2 : ℤ) : ℚ) := by
      push_cast at h ⊢
      rw [hB, ← h]; ring
    exact_mod_cast this
  have h2 : (p : ℤ) ∣ (B.den : ℤ) := by
    have : (p : ℤ) ∣ D * (B.den : ℤ) ^ 2 := ⟨q * B.num ^ 2, by rw [← h1]; ring⟩
    exact hpp.dvd_of_dvd_pow ((hpp.dvd_or_dvd this).resolve_left hD)
  obtain ⟨c, hc⟩ := h2
  have h3 : q * B.num ^ 2 = p * (D * c ^ 2) := by
    apply mul_left_cancel₀ hpp.ne_zero
    rw [hc] at h1
    linear_combination h1
  have h4 : (p : ℤ) ∣ B.num :=
    hpp.dvd_of_dvd_pow ((hpp.dvd_or_dvd ⟨_, h3⟩).resolve_left hq)
  have h5 : IsCoprime B.num (B.den : ℤ) := by
    rw [Int.isCoprime_iff_gcd_eq_one]
    simpa [Int.gcd] using B.reduced
  exact hpp.not_isUnit (h5.isUnit_of_dvd' h4 ⟨c, hc⟩)
end GlobalTheory.NormSquareRamified
