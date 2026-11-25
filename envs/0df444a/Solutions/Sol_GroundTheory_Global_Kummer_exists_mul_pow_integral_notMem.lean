-- Prove2me | solution 1 for GroundTheory.Global.Kummer.exists_mul_pow_integral_notMem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:07:20.04268+00:00
-- url     : https://prove2.me/submissions/92abbd06-7b7b-4d50-aa40-4ef119af43f1

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_KummerTheory_Unramified

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Global
open NumberField IsDedekindDomain Polynomial
open GroundTheory.Global.Kummer
variable {K : Type*} [Field K] [NumberField K]
namespace GroundTheory.Global.Kummer
theorem _root_.solution (v : HeightOneSpectrum (𝓞 K)) {n : ℕ} (hn : n ≠ 0)
    (a : Kˣ) (hav : (n : ℤ) ∣ WithZero.log (v.valuation K (a : K))) :
    ∃ c : K, c ≠ 0 ∧ ∃ b : 𝓞 K, algebraMap (𝓞 K) K b = a * c ^ n ∧ b ∉ v.asIdeal := by
  obtain ⟨m, hm⟩ := hav
  obtain ⟨π, hπ⟩ := v.valuation_exists_uniformizer K
  have hπ0 : π ≠ 0 := by
    rintro rfl
    rw [map_zero] at hπ
    exact WithZero.exp_ne_zero hπ.symm
  have ha0 : v.valuation K (a : K) ≠ 0 := by simp
  set a' : K := a * (π ^ m) ^ n with ha'
  have hva' : v.valuation K a' = 1 := by
    rw [ha', map_mul, map_pow, map_zpow₀, hπ, ← WithZero.exp_log ha0, hm]
    rw [← WithZero.exp_zsmul, ← WithZero.exp_nsmul, ← WithZero.exp_add]
    simp
  obtain ⟨r, d, hrd⟩ := HeightOneSpectrum.exists_primeCompl_mul_eq_of_integer (v := v) a' hva'.le
  have hd : (d : 𝓞 K) ∉ v.asIdeal := d.prop
  have hdK : algebraMap (𝓞 K) K d ≠ 0 := by
    intro h
    apply hd
    rw [(map_eq_zero_iff _ (IsFractionRing.injective (𝓞 K) K)).mp h]
    exact zero_mem _
  refine ⟨π ^ m * algebraMap (𝓞 K) K d, mul_ne_zero (zpow_ne_zero _ hπ0) hdK,
    r * d ^ (n - 1), ?_, ?_⟩
  · obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    rw [Nat.add_sub_cancel, map_mul, map_pow, ← hrd, ha']
    ring
  · rw [← HeightOneSpectrum.valuation_eq_one_iff_notMem (K := K) v]
    have h1 : v.valuation K (algebraMap (𝓞 K) K d) = 1 :=
      (HeightOneSpectrum.valuation_eq_one_iff_notMem (K := K) v).mpr hd
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    rw [Nat.add_sub_cancel, map_mul, map_pow, ← hrd, map_mul, map_mul, map_pow, hva', h1]
    simp
end GroundTheory.Global.Kummer
