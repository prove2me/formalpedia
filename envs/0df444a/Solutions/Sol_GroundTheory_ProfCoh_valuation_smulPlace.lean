-- Prove2me | solution 1 for GroundTheory.ProfCoh.valuation_smulPlace
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:50:18.791569+00:00
-- url     : https://prove2.me/submissions/9be6be9f-79e5-4b33-aba6-e83f7725ac1c

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_RestrictedRamification_ValuationTransport
import Theorems.Thm_GroundTheory_ProfCoh_intValuation_smulPlace

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.ProfCoh
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open scoped Pointwise
variable {F M : Type*} [Field F] [Field M] [NumberField M] [Algebra F M]
namespace GroundTheory.ProfCoh
theorem _root_.solution (σ : Gal(M/F)) (w : HeightOneSpectrum (𝓞 M)) (x : M) :
    (smulPlace σ w).valuation M (σ x) = w.valuation M x := by
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 M) x
  have ha : σ (algebraMap (𝓞 M) M a) = algebraMap (𝓞 M) M (σ • a) := rfl
  have hb' : σ (algebraMap (𝓞 M) M b) = algebraMap (𝓞 M) M (σ • b) := rfl
  rw [map_div₀, ha, hb', map_div₀, map_div₀, valuation_of_algebraMap, valuation_of_algebraMap,
    valuation_of_algebraMap, valuation_of_algebraMap, intValuation_smulPlace,
    intValuation_smulPlace]
end GroundTheory.ProfCoh
