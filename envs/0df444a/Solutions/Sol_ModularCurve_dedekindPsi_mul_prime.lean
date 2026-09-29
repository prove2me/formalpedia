-- Prove2me | solution 1 for ModularCurve.dedekindPsi_mul_prime
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/285612cb-ec51-58c8-af1e-6f42d2502110

import Mathlib
import Definitions.Def_ModularCurve_X0
import Theorems.Thm_ModularCurve_dedekindPsi_prime
import Theorems.Thm_ModularCurve_dedekindPsi_prime_pow
import Theorems.Thm_ModularCurve_dedekindPsi_mul_of_coprime
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_dedekindPsi_mul_prime
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA"
p2m_attr_erase "simp" "ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single"

set_option autoImplicit false

open ModularCurve

theorem solution (M ℓ : ℕ) [NeZero M] (hℓ : ℓ.Prime) :
    dedekindPsi (M * ℓ) = (if ℓ ∣ M then ℓ else ℓ + 1) * dedekindPsi M := by
  have hM : M ≠ 0 := NeZero.ne M
  obtain ⟨k, M', hM', rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hM ℓ hℓ.ne_one
  have hcop : Nat.Coprime (ℓ ^ k) M' := (Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd hℓ).mpr hM'))
  have hcop' : Nat.Coprime M' ℓ := ((Nat.Prime.coprime_iff_not_dvd hℓ).mpr hM').symm
  rcases Nat.eq_zero_or_pos k with rfl | hk
  ·
    simp only [pow_zero, one_mul] at hcop ⊢
    rw [if_neg hM', dedekindPsi_mul_of_coprime M' ℓ hcop', dedekindPsi_prime hℓ, mul_comm]
  ·
    have hdvd : ℓ ∣ ℓ ^ k * M' := dvd_mul_of_dvd_left (dvd_pow_self ℓ hk.ne') M'
    rw [if_pos hdvd]
    have e1 : ℓ ^ k * M' * ℓ = ℓ ^ (k + 1) * M' := by ring
    have hcop1 : Nat.Coprime (ℓ ^ (k + 1)) M' := Nat.Coprime.pow_left (k + 1) ((Nat.Prime.coprime_iff_not_dvd hℓ).mpr hM')
    rw [e1, dedekindPsi_mul_of_coprime _ _ hcop1, dedekindPsi_mul_of_coprime _ _ hcop,
      dedekindPsi_prime_pow ℓ (k + 1) hℓ (Nat.succ_ne_zero k), dedekindPsi_prime_pow ℓ k hℓ hk.ne', Nat.add_sub_cancel]
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_lt hk
    simp only [Nat.zero_add, Nat.add_sub_cancel]
    ring

end S_ModularCurve_dedekindPsi_mul_prime
end P2MW
export P2MW.S_ModularCurve_dedekindPsi_mul_prime (solution)
