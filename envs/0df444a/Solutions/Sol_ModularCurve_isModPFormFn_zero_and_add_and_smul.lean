-- Prove2me | solution 1 for ModularCurve.isModPFormFn_zero_and_add_and_smul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/d6b80438-5300-5012-add4-149b856500ca

import Mathlib
import Definitions.Def_ModularCurve_ModPFormFn
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_isModPFormFn_zero_and_add_and_smul

set_option autoImplicit false

open ModularCurve

namespace ModPFormFnClosure

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]

theorem isIntegral_pow_mul_pow_mul {e : ℕ} (he : 0 < e) (u G H : A) (hG : IsIntegral R (G ^ e * u))
    (hH : IsIntegral R (H ^ e * u)) {i : ℕ} (hi : i ≤ e) : IsIntegral R (G ^ i * H ^ (e - i) * u) := by
  refine IsIntegral.of_pow he ?_
  have : (G ^ i * H ^ (e - i) * u) ^ e = (G ^ e * u) ^ i * (H ^ e * u) ^ (e - i) := by
    rw [mul_pow, mul_pow, mul_pow, mul_pow, ← pow_mul, ← pow_mul, ← pow_mul, ← pow_mul, mul_comm i e,
      mul_comm (e - i) e]
    have hu : u ^ e = u ^ i * u ^ (e - i) := by rw [← pow_add, Nat.add_sub_cancel' hi]
    rw [hu]; ring
  rw [this]
  exact (hG.pow i).mul (hH.pow (e - i))

theorem isIntegral_add_pow_mul {e : ℕ} (u G H : A) (hG : IsIntegral R (G ^ e * u))
    (hH : IsIntegral R (H ^ e * u)) : IsIntegral R ((G + H) ^ e * u) := by
  rcases Nat.eq_zero_or_pos e with rfl | he
  · simpa using hG
  rw [add_pow, Finset.sum_mul]
  refine IsIntegral.sum _ fun i hi => ?_
  have hi' : i ≤ e := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  rw [show G ^ i * H ^ (e - i) * (e.choose i : A) * u = (e.choose i) • (G ^ i * H ^ (e - i) * u) by
    rw [nsmul_eq_mul]; ring]
  exact (isIntegral_pow_mul_pow_mul he u G H hG hH hi').nsmul _

theorem isIntegral_mul_pow_mul {e : ℕ} (u G : A) (c : R) (hG : IsIntegral R (G ^ e * u)) :
    IsIntegral R ((algebraMap R A c * G) ^ e * u) := by
  rw [mul_pow, mul_assoc, ← map_pow]
  exact isIntegral_algebraMap.mul hG

theorem isIntegral_zero_pow_mul {e : ℕ} (he : e ≠ 0) (u : A) : IsIntegral R ((0 : A) ^ e * u) := by
  rw [zero_pow he, zero_mul]; exact isIntegral_zero

end ModPFormFnClosure

open ModPFormFnClosure in
theorem solution (K : Type*) [Field K] (m : ℕ) :
    IsModPFormFn K m 0 ∧
      (∀ G H : LaurentSeries K, IsModPFormFn K m G → IsModPFormFn K m H → IsModPFormFn K m (G + H)) ∧
      (∀ (c : K) (G : LaurentSeries K), IsModPFormFn K m G → IsModPFormFn K m (c • G)) := by

  have key : ∀ (e : ℕ) (G : LaurentSeries K) (a b : ℕ),
      G ^ e * jqModC K ^ a * (jqModC K - algebraMap K (LaurentSeries K) 1728) ^ b =
        G ^ e * (jqModC K ^ a * (jqModC K - algebraMap K (LaurentSeries K) 1728) ^ b) := fun e G a b => by ring
  refine ⟨⟨?_, ?_⟩, fun G H hG hH => ⟨?_, ?_⟩, fun c G hG => ⟨?_, ?_⟩⟩
  · rw [key]; exact isIntegral_zero_pow_mul (by norm_num) _
  · rw [key]; exact isIntegral_zero_pow_mul (by norm_num) _
  · have h1 := hG.1; have h2 := hH.1
    rw [key] at h1 h2 ⊢
    exact isIntegral_add_pow_mul _ G H h1 h2
  · have h1 := hG.2; have h2 := hH.2
    rw [key] at h1 h2 ⊢
    exact isIntegral_add_pow_mul _ G H h1 h2
  · have h1 := hG.1
    rw [key] at h1 ⊢

    have e1 : c • G = algebraMap (↥(Algebra.adjoin K ({jqModC K} : Set (LaurentSeries K)))) (LaurentSeries K)
        (algebraMap K _ c) * G := by
      have e0 : c • G = algebraMap K (LaurentSeries K) c * G := by
        rw [HahnSeries.algebraMap_apply', show algebraMap K (PowerSeries K) c = PowerSeries.C c by simp,
          HahnSeries.ofPowerSeries_C, HahnSeries.C_mul_eq_smul]
      rw [e0]; rfl
    rw [e1]; exact isIntegral_mul_pow_mul _ G _ h1
  · have h1 := hG.2
    rw [key] at h1 ⊢
    have e1 : c • G = algebraMap (↥(Algebra.adjoin K ({(jqModC K)⁻¹} : Set (LaurentSeries K)))) (LaurentSeries K)
        (algebraMap K _ c) * G := by
      have e0 : c • G = algebraMap K (LaurentSeries K) c * G := by
        rw [HahnSeries.algebraMap_apply', show algebraMap K (PowerSeries K) c = PowerSeries.C c by simp,
          HahnSeries.ofPowerSeries_C, HahnSeries.C_mul_eq_smul]
      rw [e0]; rfl
    rw [e1]; exact isIntegral_mul_pow_mul _ G _ h1

end S_ModularCurve_isModPFormFn_zero_and_add_and_smul
end P2MW
export P2MW.S_ModularCurve_isModPFormFn_zero_and_add_and_smul (solution)
