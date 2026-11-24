-- Prove2me | solution 1 for GlobalTheory.NormMod.exists_norm_mod_level
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T19:14:40.583501+00:00
-- url     : https://prove2.me/submissions/1b099a86-f2b0-4e7b-ad53-bb50d158c7dc

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_IsCoprimeTwoSubRtTwoAddRt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsHostNormModCoprimeLevelHalf

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
theorem _root_.solution (l : Level H) (ν : ℤ) :
    ∃ t : 𝓞 E, (l.M : 𝓞 E) ∣ t * H.bar t - (ν : 𝓞 E) ∧ t - 1 ∈ l.Mb := by
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.1 ((Ideal.eq_top_iff_one _).1 l.coprime)
  have ha' : H.bar a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) := Ideal.mem_map_of_mem _ ha
  have hb' : H.bar b ∈ l.Mb := by
    obtain ⟨c, hc, rfl⟩ := (Ideal.mem_map_iff_of_surjective (H.bar : 𝓞 E →+* 𝓞 E) H.bar.surjective).1 hb
    simpa using hc
  have hab' := congrArg H.bar hab
  rw [map_add, map_one] at hab'
  refine ⟨b + ν * a, ?_, ?_⟩
  · rw [← Ideal.mem_span_singleton, ← l.prod]
    have h := Ideal.add_mem _
      (Ideal.mul_mem_left _ (1 - (ν : 𝓞 E)) (Ideal.mul_mem_mul hb' hb))
      (Ideal.mul_mem_left _ ((ν : 𝓞 E) ^ 2 - ν) (Ideal.mul_mem_mul ha ha'))
    convert h using 1
    rw [map_add, map_mul, map_intCast]
    linear_combination (ν : 𝓞 E) * (H.bar a + H.bar b) * hab + (ν : 𝓞 E) * hab'
  · convert l.Mb.mul_mem_left ((ν : 𝓞 E) - 1) ha using 1
    linear_combination hab
end GlobalTheory.NormMod
