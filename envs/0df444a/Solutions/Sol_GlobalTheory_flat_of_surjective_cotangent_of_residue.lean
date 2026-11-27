-- Prove2me | solution 1 for GlobalTheory.flat_of_surjective_cotangent_of_residue
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T04:39:07.624148+00:00
-- url     : https://prove2.me/submissions/f86bfff1-c319-4601-8d5b-7fc83271bd2c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsUniqueFactorCompletedStalkOfMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsMemPowSubMemPowSucc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IdealEqBotOfFlatQuotientOfMapMaximalIdeal
import Theorems.Thm_GlobalTheory_flat_of_surjective_cotangent

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
variable {A : Type*} [CommRing A]
variable {B : Type*} [CommRing B] {φ : A →+* B} {I : Ideal A} {J : Ideal B}
variable [IsNoetherianRing A] {φ : A →+* A}
namespace GlobalTheory
theorem _root_.solution {k : Type*} [CommRing k] [Algebra k A]
    [IsLocalRing A] (hk : Function.Surjective (algebraMap k (ResidueField A))) (φ : A →ₐ[k] A)
    (hle : maximalIdeal A ≤ (maximalIdeal A).comap φ)
    (h₁ : Function.Surjective (Ideal.mapCotangent _ _ φ hle)) : (φ : A →+* A).Flat := by
  haveI : IsLocalHom (φ : A →+* A) := ((local_hom_TFAE (φ : A →+* A)).out 0 3).mpr hle
  refine (flat_of_surjective_cotangent φ hle (fun x => ?_) h₁).2
  obtain ⟨c, rfl⟩ := hk x
  refine ⟨algebraMap k _ c, ?_⟩
  change residue A (φ (algebraMap k A c)) = residue A (algebraMap k A c)
  rw [φ.commutes]
end GlobalTheory
