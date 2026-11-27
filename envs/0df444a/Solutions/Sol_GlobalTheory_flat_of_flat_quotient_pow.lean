-- Prove2me | solution 1 for GlobalTheory.flat_of_flat_quotient_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T04:38:39.414962+00:00
-- url     : https://prove2.me/submissions/afa51fe7-8337-443e-91ce-8723d27b67ee

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsUniqueFactorCompletedStalkOfMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsMemPowSubMemPowSucc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IdealEqBotOfFlatQuotientOfMapMaximalIdeal
import Theorems.Thm_GlobalTheory_LocalFlat_relationsLift_of_flat
import Theorems.Thm_GlobalTheory_LocalFlat_flat_of_relationsLift

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
theorem _root_.solution {A : Type u} (B : Type v) {M : Type w} [CommRing A] [CommRing B]
    [Algebra A B] [IsNoetherianRing A] [IsNoetherianRing B] [AddCommGroup M] [Module A M]
    [Module B M] [IsScalarTower A B M] [Module.Finite B M] {I : Ideal A}
    (hI : I.map (algebraMap A B) ≤ Ideal.jacobson ⊥)
    (h : ∀ n : ℕ, Module.Flat (A ⧸ I ^ n) (M ⧸ (I ^ n • ⊤ : Submodule A M))) :
    Module.Flat A M :=
  LocalFlat.flat_of_relationsLift B hI fun n =>
    haveI := h n
    LocalFlat.relationsLift_of_flat (C := A ⧸ I ^ n) Ideal.Quotient.mk_surjective
      Ideal.mk_ker (Submodule.mkQ _) (Submodule.mkQ_surjective _) (Submodule.ker_mkQ _)
end GlobalTheory
