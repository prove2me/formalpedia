-- Prove2me | solution 1 for NumberField.natAbs_discr_le_of_quartic_cyclotomic_tower
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:56:00.627382+00:00
-- url     : https://prove2.me/submissions/5c78cdaf-9c7c-4432-ad24-fedcf333c0d5

import Mathlib

set_option autoImplicit false

namespace NumberField

/-- The discriminant tower formula gives the required quintic bound from a
quartic overfield of absolute discriminant `5^35`, without a conductor formula. -/
theorem _root_.solution
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] (hdegree : Module.finrank K L = 4)
    (hdiscr : (discr L).natAbs = 5 ^ 35) :
    (discr K).natAbs ≤ 5 ^ 8 := by
  have htower := natAbs_discr_eq_absNorm_differentIdeal_mul_natAbs_discr_pow
    K (𝓞 K) L (𝓞 L)
  rw [hdegree, hdiscr] at htower
  have hdvd : (discr K).natAbs ^ 4 ∣ 5 ^ 35 :=
    ⟨Ideal.absNorm (differentIdeal (𝓞 K) (𝓞 L)), htower.trans (mul_comm _ _)⟩
  have hbase : (discr K).natAbs ∣ 5 ^ 35 :=
    dvd_trans (dvd_pow_self _ (by decide : 4 ≠ 0)) hdvd
  obtain ⟨k, _, hk⟩ := (Nat.dvd_prime_pow (by decide : Nat.Prime 5)).mp hbase
  rw [hk, ← pow_mul] at hdvd
  have hle : 5 ^ (k * 4) ≤ 5 ^ 35 := Nat.le_of_dvd (by positivity) hdvd
  have hkbound : k * 4 ≤ 35 := (Nat.pow_le_pow_iff_right (by decide : 1 < 5)).mp hle
  rw [hk]
  exact (Nat.pow_le_pow_iff_right (by decide : 1 < 5)).2 (by omega)

end NumberField
