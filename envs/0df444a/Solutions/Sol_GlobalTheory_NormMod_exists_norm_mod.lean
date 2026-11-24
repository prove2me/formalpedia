-- Prove2me | solution 1 for GlobalTheory.NormMod.exists_norm_mod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T20:57:11.270684+00:00
-- url     : https://prove2.me/submissions/fab09399-878a-4de9-89e4-47947f9c44e1

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_IsCoprimeTwoSubRtTwoAddRt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsHostNormModCoprimeLevelHalf
import Theorems.Thm_GlobalTheory_NormMod_exists_norm_mod_mul
import Theorems.Thm_GlobalTheory_NormMod_exists_norm_mod_level

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
theorem _root_.solution (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (l : Level H)
    (n : ℕ) (ν : ℤ) (hn : 0 < n) (hν : IsCoprime ν (n : ℤ)) :
    ∃ t : 𝓞 E, (n : 𝓞 E) ∣ t * H.bar t - (ν : 𝓞 E) ∧ (l.M ∣ n → t - 1 ∈ l.Mb) := by
  by_cases hM : l.M ∣ n
  · obtain ⟨k, rfl⟩ := hM
    obtain ⟨t, ht, ht1⟩ := exists_norm_mod_level H l ν
    push_cast at hν
    obtain ⟨s, hs, c, hc⟩ := exists_norm_mod_mul H (right_ne_zero_of_mul hn.ne')
      hν.of_mul_right_right (left_ne_zero_of_mul hn.ne') ht
    refine ⟨s, hs, fun _ => ?_⟩
    have hMb : (l.M : 𝓞 E) ∈ l.Mb := by
      have h := Ideal.mem_span_singleton_self (l.M : 𝓞 E)
      rw [← l.prod] at h
      exact (Ideal.mul_le_inf (I := l.Mb) h).1
    convert l.Mb.add_mem ht1 (l.Mb.mul_mem_right c hMb) using 1
    linear_combination hc
  · obtain ⟨s, hs, -⟩ := exists_norm_mod_mul H hn.ne' hν (m := 1) one_ne_zero (t := 1) (by simp)
    exact ⟨s, by simpa using hs, fun h => absurd h hM⟩
end GlobalTheory.NormMod
