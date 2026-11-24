-- Prove2me | solution 1 for GlobalTheory.exists_ringHom_extension_of_isIntegral
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:46:55.060213+00:00
-- url     : https://prove2.me/submissions/d9fe0afe-5fb3-4aa9-a22a-66fa2a243007

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsFreeRingActionIffInertiaEqBotOfIsPrime
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsIsoNormalizationPullbackOfToIntegralClosure
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_IsOpenOfMemIrreducibleComponentsOfFinite
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_IsDomainAndIsIntegrallyClosedLocalizationOfIsInv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u v
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open GlobalTheory
variable {G : Type*} [Group G] [Finite G] {A k : Type*} [CommRing A] [MulSemiringAction G A]
  [CommRing k] [IsDomain k]
namespace GlobalTheory
theorem _root_.solution {B A k : Type*} [CommRing B] [CommRing A] [Field k]
    [IsAlgClosed k] [Algebra B A] [FaithfulSMul B A] [Algebra.IsIntegral B A] (φ : B →+* k) :
    ∃ ψ : A →+* k, ψ.comp (algebraMap B A) = φ := by
  have := RingHom.ker_isPrime φ
  obtain ⟨⟨Q, hQ⟩, hQφ⟩ := Algebra.IsIntegral.comap_surjective B A ⟨RingHom.ker φ, ‹_›⟩
  have : Q.LiesOver (RingHom.ker φ) := ⟨congr($(hQφ).asIdeal).symm⟩
  let := (RingHom.kerLift φ).toAlgebra
  have : FaithfulSMul (B ⧸ RingHom.ker φ) k :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr (RingHom.kerLift_injective φ)
  have : IsDomain (A ⧸ Q) := inferInstance
  have : IsDomain (B ⧸ RingHom.ker φ) := inferInstance
  have : Module.IsTorsionFree (B ⧸ RingHom.ker φ) (A ⧸ Q) :=
    Module.isTorsionFree_iff_faithfulSMul.mpr inferInstance
  have : Module.IsTorsionFree (B ⧸ RingHom.ker φ) k :=
    Module.isTorsionFree_iff_faithfulSMul.mpr inferInstance
  have : Algebra.IsIntegral (B ⧸ RingHom.ker φ) (A ⧸ Q) := ⟨fun x ↦ by
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact ((Algebra.IsIntegral.isIntegral (R := B) a).map
      (Ideal.Quotient.mkₐ B Q)).tower_top⟩
  have : Algebra.IsAlgebraic (B ⧸ RingHom.ker φ) (A ⧸ Q) := Algebra.IsIntegral.isAlgebraic
  let ψ : (A ⧸ Q) →ₐ[B ⧸ RingHom.ker φ] k := IsAlgClosed.lift
  exact ⟨(ψ : A ⧸ Q →+* k).comp (Ideal.Quotient.mk Q),
    RingHom.ext fun b ↦ ψ.commutes (Ideal.Quotient.mk _ b)⟩
end GlobalTheory
