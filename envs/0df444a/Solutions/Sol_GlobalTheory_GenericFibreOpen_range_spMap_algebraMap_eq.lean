-- Prove2me | solution 1 for GlobalTheory.GenericFibreOpen.range_spMap_algebraMap_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T16:18:19.382522+00:00
-- url     : https://prove2.me/submissions/d48a758c-cdec-4159-b600-aac59295573e

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsCompletedStrictHens
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_PreimageGenericFiberIsOpen

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.GenericFibreOpen
namespace GlobalTheory.GenericFibreOpen
theorem _root_.solution (O K : Type) [CommRing O] [IsDomain O] [Field K] [Algebra O K]
    [IsFractionRing O K] :
    Set.range (spMap (algebraMap O K)) = {x : Sp O | (x : PrimeSpectrum O).asIdeal = ⊥} := by
  have key : ∀ y : Sp K, ((spMap (algebraMap O K)).base y : PrimeSpectrum O).asIdeal = ⊥ := fun y => by
    change Ideal.comap (algebraMap O K) (y : PrimeSpectrum K).asIdeal = ⊥
    rw [(Ideal.eq_bot_or_top (y : PrimeSpectrum K).asIdeal).resolve_right (y : PrimeSpectrum K).isPrime.ne_top]
    exact Ideal.comap_bot_of_injective _ (IsFractionRing.injective O K)
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact key y
  · intro hx
    refine ⟨(show Sp K from (default : PrimeSpectrum K)), ?_⟩
    apply PrimeSpectrum.ext
    exact (key _).trans hx.symm
end GlobalTheory.GenericFibreOpen
