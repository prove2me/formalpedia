-- Prove2me | solution 1 for GlobalTheory.specMap_apply_eq_bot
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:44:57.467242+00:00
-- url     : https://prove2.me/submissions/3409485c-e285-41c4-b223-0e07ffe9c85f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsValuationSubringLiftOfSpecialFibre

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
open GlobalTheory
universe u
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
variable {O K : Type u} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K]
  [Algebra O K] [IsFractionRing O K]
namespace GlobalTheory
theorem _root_.solution {R F : Type u} [CommRing R] [IsDomain R] [Field F] (g : R →+* F)
    (hg : Function.Injective g) (t : Spec (.of F)) :
    Spec.map (CommRingCat.ofHom g) t = (⊥ : PrimeSpectrum R) := by
  refine PrimeSpectrum.ext ?_
  have ht : t.asIdeal = ⊥ := @Ideal.eq_bot_of_prime F _ t.asIdeal t.isPrime
  exact (congrArg (Ideal.comap g) ht).trans (Ideal.comap_bot_of_injective _ hg)
end GlobalTheory
