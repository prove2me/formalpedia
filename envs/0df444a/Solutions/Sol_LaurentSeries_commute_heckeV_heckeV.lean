-- Prove2me | solution 1 for LaurentSeries.commute_heckeV_heckeV
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/5cdffe29-a536-5983-9b7b-7dc8bba46f9f

import Mathlib
import Definitions.Def_LaurentSeries_HeckeU
import Definitions.Def_LaurentSeries_HeckeV
import Definitions.Def_ModularCurve_X0
import Definitions.Def_ModularCurve_LaurentCoeff
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LaurentSeries_commute_heckeV_heckeV

set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

set_option autoImplicit false

open ModularCurve LaurentSeries

theorem solution (R : Type*) [CommRing R] (ℓ ℓ' : ℕ) (hℓ : 0 < ℓ) (hℓ' : 0 < ℓ')
    (h : Nat.Coprime ℓ ℓ') :
    Commute (heckeV R ℓ hℓ) (heckeV R ℓ' hℓ')  := by
  have cop : IsCoprime (ℓ : ℤ) (ℓ' : ℤ) := Nat.isCoprime_iff_coprime.mpr h
  have hℓ0 : (ℓ : ℤ) ≠ 0 := by exact_mod_cast hℓ.ne'
  have hℓ0' : (ℓ' : ℤ) ≠ 0 := by exact_mod_cast hℓ'.ne'

  have key : ∀ (a b : ℕ) (ha : 0 < a) (hb : 0 < b), IsCoprime (a : ℤ) (b : ℤ) → (a : ℤ) ≠ 0 → (b : ℤ) ≠ 0 →
      ∀ (f : LaurentSeries R) (n : ℤ), (heckeV R a ha (heckeV R b hb f)).coeff n =
        if (a : ℤ) * b ∣ n then f.coeff (n / ((a : ℤ) * b)) else 0 := by
    intro a b ha hb hab ha0 hb0 f n
    rw [coeff_heckeV]
    by_cases h1 : (a : ℤ) ∣ n
    · obtain ⟨m, rfl⟩ := h1
      rw [if_pos ⟨m, rfl⟩, Int.mul_ediv_cancel_left _ ha0, coeff_heckeV]
      by_cases h2 : (b : ℤ) ∣ m
      · obtain ⟨k, rfl⟩ := h2
        rw [if_pos ⟨k, rfl⟩, Int.mul_ediv_cancel_left _ hb0, if_pos ⟨k, by ring⟩,
          show (a : ℤ) * (b * k) = (a * b) * k by ring, Int.mul_ediv_cancel_left _ (mul_ne_zero ha0 hb0)]
      · rw [if_neg h2, if_neg]
        rintro ⟨k, hk⟩
        apply h2
        refine ⟨k, ?_⟩
        have : (a : ℤ) * m = a * (b * k) := by rw [hk]; ring
        exact mul_left_cancel₀ ha0 this
    · rw [if_neg h1, if_neg]
      rintro ⟨k, hk⟩
      exact h1 ⟨b * k, by rw [hk]; ring⟩
  ext f n
  rw [Module.End.mul_apply, Module.End.mul_apply, key ℓ ℓ' hℓ hℓ' cop hℓ0 hℓ0' f n,
    key ℓ' ℓ hℓ' hℓ cop.symm hℓ0' hℓ0 f n, mul_comm]

end S_LaurentSeries_commute_heckeV_heckeV
end P2MW
export P2MW.S_LaurentSeries_commute_heckeV_heckeV (solution)
