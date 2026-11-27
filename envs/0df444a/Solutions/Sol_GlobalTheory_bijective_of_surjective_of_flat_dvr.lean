-- Prove2me | solution 1 for GlobalTheory.bijective_of_surjective_of_flat_dvr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:37:03.657736+00:00
-- url     : https://prove2.me/submissions/08f8b442-4611-440c-8d72-a20b50088a4c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsUniqueFactorCompletedStalkOfMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsMemPowSubMemPowSucc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IdealEqBotOfFlatQuotientOfMapMaximalIdeal
import Theorems.Thm_GlobalTheory_ideal_eq_bot_of_flat_quotient

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct LinearMap
open GlobalTheory
universe u v w
open IsLocalRing
namespace GlobalTheory
theorem _root_.solution {T R S : Type*} [CommRing T] [IsDomain T]
    [IsDiscreteValuationRing T] [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Algebra T R] [IsLocalHom (algebraMap T R)] [CommRing S] [Nontrivial S] [Algebra T S]
    [Module.Flat T S] (q : R →ₐ[T] S) (hq : Function.Surjective q) : Function.Bijective q := by
  haveI : Module.Flat T (R ⧸ RingHom.ker q) :=
    Module.Flat.of_linearEquiv (Ideal.quotientKerAlgEquivOfSurjective hq).toLinearEquiv
  exact ⟨(RingHom.injective_iff_ker_eq_bot q).mpr
    (ideal_eq_bot_of_flat_quotient T (RingHom.ker_ne_top q)), hq⟩
end GlobalTheory
