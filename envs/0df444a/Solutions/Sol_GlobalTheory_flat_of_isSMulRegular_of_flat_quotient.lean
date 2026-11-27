-- Prove2me | solution 1 for GlobalTheory.flat_of_isSMulRegular_of_flat_quotient
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T04:38:51.466441+00:00
-- url     : https://prove2.me/submissions/51bc0181-ea06-4419-a002-8517aa3cf98a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsUniqueFactorCompletedStalkOfMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsMemPowSubMemPowSucc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IdealEqBotOfFlatQuotientOfMapMaximalIdeal
import Theorems.Thm_GlobalTheory_LocalFlat_relationsLift_of_flat
import Theorems.Thm_GlobalTheory_LocalFlat_relationsLift_pow
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
theorem _root_.solution {A : Type u} (B : Type v) {M : Type w} [CommRing A]
    [CommRing B] [Algebra A B] [IsNoetherianRing A] [IsNoetherianRing B] [AddCommGroup M]
    [Module A M] [Module B M] [IsScalarTower A B M] [Module.Finite B M] {π : A}
    (hπ : algebraMap A B π ∈ Ideal.jacobson (⊥ : Ideal B)) (hreg : IsSMulRegular M π)
    [Module.Flat (A ⧸ Ideal.span {π}) (M ⧸ (Ideal.span {π} • ⊤ : Submodule A M))] :
    Module.Flat A M :=
  LocalFlat.flat_of_relationsLift B (I := Ideal.span {π})
    (by rwa [Ideal.map_span, Set.image_singleton, Ideal.span_singleton_le_iff_mem])
    (LocalFlat.relationsLift_pow
      (LocalFlat.relationsLift_of_flat (C := A ⧸ Ideal.span {π}) Ideal.Quotient.mk_surjective
        Ideal.mk_ker (Submodule.mkQ _) (Submodule.mkQ_surjective _) (Submodule.ker_mkQ _)) hreg)
end GlobalTheory
