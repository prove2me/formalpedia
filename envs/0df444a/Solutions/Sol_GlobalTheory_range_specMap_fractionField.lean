-- Prove2me | solution 1 for GlobalTheory.range_specMap_fractionField
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:30:35.738061+00:00
-- url     : https://prove2.me/submissions/3d34c947-9256-4839-8d0c-da7418167ed5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsValuationSubringLiftOfSpecialFibre
import Theorems.Thm_GlobalTheory_specMap_apply_eq_bot

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
theorem _root_.solution :
    Set.range (Spec.map (CommRingCat.ofHom (algebraMap O K))) =
      {x : Spec (.of O) | x ≠ closedPoint O} := by
  have hbot := specMap_apply_eq_bot _ (IsFractionRing.injective O K)
  ext x
  constructor
  · rintro ⟨t, rfl⟩ e
    rw [hbot] at e
    exact IsDiscreteValuationRing.not_a_field O (congrArg PrimeSpectrum.asIdeal e).symm
  · intro hx
    refine ⟨closedPoint K, (hbot _).trans ?_⟩
    by_contra hne
    have h0 : x.asIdeal ≠ ⊥ := fun e => hne (PrimeSpectrum.ext e.symm)
    exact hx (PrimeSpectrum.ext (eq_maximalIdeal (x.isPrime.isMaximal h0)))
end GlobalTheory
