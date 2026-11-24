-- Prove2me | solution 1 for GlobalTheory.NormMod.exists_norm_mod_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T20:42:43.024426+00:00
-- url     : https://prove2.me/submissions/f28412a4-6618-4018-9b4a-1e036c242df8

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_IsCoprimeTwoSubRtTwoAddRt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsHostNormModCoprimeLevelHalf
import Theorems.Thm_GlobalTheory_NormMod_exists_norm_mod_mul_prime

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
theorem _root_.solution {k : ℕ} (hk : k ≠ 0) {ν : ℤ} (hν : IsCoprime ν (k : ℤ)) :
    ∀ {m : ℕ}, m ≠ 0 → ∀ {t : 𝓞 E}, (m : 𝓞 E) ∣ t * H.bar t - (ν : 𝓞 E) →
      ∃ s : 𝓞 E, ((m * k : ℕ) : 𝓞 E) ∣ s * H.bar s - (ν : 𝓞 E) ∧ (m : 𝓞 E) ∣ s - t := by
  induction k using induction_on_primes with
  | zero => exact absurd rfl hk
  | one => exact fun _ t ht => ⟨t, by simpa using ht, by simp⟩
  | prime_mul p k hp ih =>
    intro m hm t ht
    push_cast at hν
    obtain ⟨s, hs, hst⟩ := exists_norm_mod_mul_prime H hm hp hν.of_mul_right_left ht
    obtain ⟨u, hu, hus⟩ := ih (right_ne_zero_of_mul hk) hν.of_mul_right_right
      (mul_ne_zero hm hp.ne_zero) hs
    refine ⟨u, by rwa [← mul_assoc], ?_⟩
    push_cast at hus
    simpa using dvd_add (dvd_of_mul_right_dvd hus) hst
end GlobalTheory.NormMod
