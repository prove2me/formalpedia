-- Prove2me | solution 1 for LaurentSeries.eq_zero_of_heckeT_eq_smul_of_heckeU_eq_smul_of_coeff_one_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/886ccb4b-c5a4-5de5-b489-ce7c586225e1

import Mathlib
import Definitions.Def_LaurentSeries_HeckeU
import Definitions.Def_LaurentSeries_HeckeV
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LaurentSeries_eq_zero_of_heckeT_eq_smul_of_heckeU_eq_smul_of_coeff_one_eq_zero

set_option autoImplicit false

theorem solution
    (R : Type*) [CommRing R] (M k : ℕ) (θ : Nat.Primes → R) (f : LaurentSeries R)
    (hneg : ∀ n : ℤ, n ≤ 0 → f.coeff n = 0)
    (hT : ∀ ℓ : Nat.Primes, ¬ (ℓ : ℕ) ∣ M → LaurentSeries.heckeT R (ℓ : ℕ) ℓ.2.pos k f = θ ℓ • f)
    (hU : ∀ q : Nat.Primes, (q : ℕ) ∣ M → LaurentSeries.heckeU R (q : ℕ) q.2.pos f = θ q • f)
    (h1 : f.coeff 1 = 0) :
    f = 0 := by

  have key : ∀ m : ℕ, f.coeff (m : ℤ) = 0 := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      rcases Nat.lt_or_ge m 2 with hm | hm
      · interval_cases m
        · exact hneg 0 le_rfl
        · exact_mod_cast h1
      · obtain ⟨ℓ, hℓ, hℓm⟩ := Nat.exists_prime_and_dvd (show m ≠ 1 by omega)
        obtain ⟨m', rfl⟩ := hℓm
        have hℓpos : 0 < ℓ := hℓ.pos
        have hm' : m' < ℓ * m' := by
          have : 1 < ℓ := hℓ.one_lt
          have hm'pos : 0 < m' := Nat.pos_of_ne_zero (by rintro rfl; simp at hm)
          nlinarith
        by_cases hℓN : ℓ ∣ M
        ·
          have := congrArg (fun g : LaurentSeries R => g.coeff (m' : ℤ)) (hU ⟨ℓ, hℓ⟩ hℓN)
          simp only [LaurentSeries.coeff_heckeU, HahnSeries.coeff_smul, smul_eq_mul] at this
          rw [ih m' hm', mul_zero] at this
          exact_mod_cast this
        ·
          have := congrArg (fun g : LaurentSeries R => g.coeff (m' : ℤ)) (hT ⟨ℓ, hℓ⟩ hℓN)
          simp only [LaurentSeries.coeff_heckeT, HahnSeries.coeff_smul, smul_eq_mul] at this
          rw [ih m' hm', mul_zero] at this
          have hif : (if ((ℓ : ℕ) : ℤ) ∣ (m' : ℤ) then f.coeff ((m' : ℤ) / (ℓ : ℕ)) else 0) = 0 := by
            split_ifs with hd
            · obtain ⟨c, hc⟩ := Int.natCast_dvd_natCast.mp hd
              have hcm : c < ℓ * m' := by
                rcases Nat.eq_zero_or_pos c with rfl | hc0
                · simp at hc; subst hc; exact Nat.pos_of_ne_zero (by omega)
                · calc c ≤ ℓ * c := Nat.le_mul_of_pos_left c hℓpos
                    _ = m' := hc.symm
                    _ < ℓ * m' := hm'
              have : (m' : ℤ) / (ℓ : ℕ) = (c : ℤ) := by
                rw [hc]; push_cast; rw [Int.mul_ediv_cancel_left _ (by exact_mod_cast hℓ.ne_zero)]
              rw [this]; exact ih c hcm
            · rfl
          rw [hif, mul_zero, add_zero] at this
          exact_mod_cast this
  ext n
  rcases le_or_gt n 0 with hn | hn
  · simpa using hneg n hn
  · lift n to ℕ using hn.le
    simpa using key n

end S_LaurentSeries_eq_zero_of_heckeT_eq_smul_of_heckeU_eq_smul_of_coeff_one_eq_zero
end P2MW
export P2MW.S_LaurentSeries_eq_zero_of_heckeT_eq_smul_of_heckeU_eq_smul_of_coeff_one_eq_zero (solution)
