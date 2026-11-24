-- Prove2me | solution 1 for GlobalTheory.NormMod.exists_norm_mod_mul_prime
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T20:24:39.985012+00:00
-- url     : https://prove2.me/submissions/b0b8fd4f-9bde-496f-b241-5438b6428a2c

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_IsCoprimeTwoSubRtTwoAddRt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsHostNormModCoprimeLevelHalf
import Theorems.Thm_GlobalTheory_NormMod_exists_norm_mod_prime

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.NormMod
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.HostModel
open scoped TensorProduct
variable {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E)
namespace GlobalTheory.NormMod
theorem _root_.solution {m p : ℕ} (hm : m ≠ 0) (hp : p.Prime) {ν : ℤ}
    (hν : IsCoprime ν (p : ℤ)) {t : 𝓞 E} (ht : (m : 𝓞 E) ∣ t * H.bar t - (ν : 𝓞 E)) :
    ∃ s : 𝓞 E, ((m * p : ℕ) : 𝓞 E) ∣ s * H.bar s - (ν : 𝓞 E) ∧ (m : 𝓞 E) ∣ s - t := by
  obtain ⟨y, hy⟩ := ht
  by_cases hpm : p ∣ m
  · obtain ⟨c, hc⟩ := hpm
    have hc' : (m : 𝓞 E) = p * c := by exact_mod_cast hc
    have hy' : H.bar y = y := by
      have h := congrArg H.bar hy
      rw [map_sub, map_mul, bar_bar, map_intCast, map_mul, map_natCast] at h
      apply mul_left_cancel₀ (Nat.cast_ne_zero.2 hm : (m : 𝓞 E) ≠ 0)
      linear_combination hy - h
    obtain ⟨a, b, hab⟩ := hν
    have hab' := congrArg (Int.cast : ℤ → 𝓞 E) hab
    push_cast at hab'
    refine ⟨t * (1 - m * y * a * H.w0), ⟨y * b - c * y * y * a
      + c * (y * a) ^ 2 * (H.w0 * (1 - H.w0)) * (t * H.bar t), ?_⟩, ⟨-(t * y * a * H.w0), by ring⟩⟩
    simp only [map_mul, map_sub, map_one, map_natCast, map_intCast, hy', cmHost_bar_halfIntegerGenerator]
    push_cast
    linear_combination (1 - m * y * a) * hy - m * y * hab'
      + (m * (-(y * y * a) + (y * a) ^ 2 * (H.w0 * (1 - H.w0)) * (t * H.bar t))) * hc'
  · obtain ⟨s, z, hz⟩ := exists_norm_mod_prime H hp hν
    have hco : IsCoprime (m : 𝓞 E) (p : 𝓞 E) :=
      ((Nat.coprime_comm.1 (hp.coprime_iff_not_dvd.2 hpm)).isCoprime.map
        (Int.castRingHom (𝓞 E))).imp fun a ⟨b, h⟩ => ⟨b, by simpa using h⟩
    obtain ⟨a, b, hab⟩ := id hco
    have cong : ∀ (k : ℕ) (u v : 𝓞 E), (k : 𝓞 E) ∣ u - v → (k : 𝓞 E) ∣ v * H.bar v - ν →
        (k : 𝓞 E) ∣ u * H.bar u - ν := by
      rintro k u v ⟨w, hw⟩ h
      have h2 := congrArg H.bar hw
      rw [map_sub, map_mul, map_natCast] at h2
      have := dvd_add h (Dvd.intro (w * H.bar u + v * H.bar w) rfl : (k : 𝓞 E) ∣ _)
      convert this using 1
      linear_combination H.bar u * hw + v * h2
    have d1 : (m : 𝓞 E) ∣ (b * p * t + a * m * s) - t :=
      ⟨a * (s - t), by linear_combination t * hab⟩
    have d2 : (p : 𝓞 E) ∣ (b * p * t + a * m * s) - s :=
      ⟨b * (t - s), by linear_combination s * hab⟩
    refine ⟨b * p * t + a * m * s, ?_, d1⟩
    push_cast
    exact hco.mul_dvd (cong _ _ _ d1 ⟨y, hy⟩) (cong _ _ _ d2 ⟨z, hz⟩)
end GlobalTheory.NormMod
