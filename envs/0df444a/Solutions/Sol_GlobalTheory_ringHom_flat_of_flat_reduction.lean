-- Prove2me | solution 1 for GlobalTheory.ringHom_flat_of_flat_reduction
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:32:45.739852+00:00
-- url     : https://prove2.me/submissions/b8791eec-7f2d-4851-ac01-461ea7acddf0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsUniqueFactorCompletedStalkOfMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsMemPowSubMemPowSucc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IdealEqBotOfFlatQuotientOfMapMaximalIdeal
import Theorems.Thm_GlobalTheory_LocalFlat_relationsLift_pow
import Theorems.Thm_GlobalTheory_LocalFlat_flat_of_relationsLift
import Theorems.Thm_GlobalTheory_LocalFlat_relationsLift_of_square
import Theorems.Thm_GlobalTheory_IsAdicFamily_comp


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
variable {A B : Type*} [CommRing A] [CommRing B] [IsNoetherianRing A] [IsNoetherianRing B]
namespace GlobalTheory
theorem _root_.solution {C D : Type*} [CommRing C] [CommRing D] (φ : A →+* B)
    {π : A} (hπ : φ π ∈ Ideal.jacobson (⊥ : Ideal B)) (hreg : IsSMulRegular B (φ π))
    (p : A →+* C) (q : B →+* D) (ψ : C →+* D)
    (hp : Function.Surjective p) (hq : Function.Surjective q)
    (hpπ : RingHom.ker p = Ideal.span {π}) (hqπ : RingHom.ker q = Ideal.span {φ π})
    (hsq : ψ.comp p = q.comp φ) (hψ : ψ.Flat) : φ.Flat := by
  letI := φ.toAlgebra
  have hmap : (Ideal.span {π}).map (algebraMap A B) = Ideal.span {φ π} := by
    rw [Ideal.map_span, Set.image_singleton]
    rfl
  refine LocalFlat.flat_of_relationsLift B (I := Ideal.span {π})
    (by rwa [hmap, Ideal.span_singleton_le_iff_mem]) (LocalFlat.relationsLift_pow ?_ hreg)
  exact LocalFlat.relationsLift_of_square p q ψ hp hq hpπ (hqπ.trans hmap.symm) hsq hψ
end GlobalTheory
