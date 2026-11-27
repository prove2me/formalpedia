-- Prove2me | solution 1 for GlobalTheory.free_action_etale_and_descent
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T04:39:40.415007+00:00
-- url     : https://prove2.me/submissions/50bb673c-3dfd-482c-9f92-56857d20d67a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsUnitSmulEqOfBijectiveToSpanSingleton
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsFreeRingActionIffInertiaEqBotOfIsPrime
import Theorems.Thm_GlobalTheory_FreeQuotient_tame_descent
import Theorems.Thm_GlobalTheory_FreeQuotient_bijective_liftBaseChange_of_isBaseChange
import Theorems.Thm_GlobalTheory_FreeQuotient_finite_and_projective
import Theorems.Thm_GlobalTheory_FreeQuotient_faithfullyFlat
import Theorems.Thm_GlobalTheory_FreeQuotient_etale
import Theorems.Thm_GlobalTheory_FreeQuotient_rankAtStalk_eq_card
import Theorems.Thm_GlobalTheory_FreeQuotient_isBaseChange_invariants
import Theorems.Thm_GlobalTheory_FreeQuotient_finite_projective_invariants_iff
import Theorems.Thm_GlobalTheory_FreeQuotient_bijective_toInvariantsTensor
import Theorems.Thm_GlobalTheory_SemilinearModule_invariantsFunctor_isEquivalence

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
open GlobalTheory
universe w v u
open CategoryTheory
namespace GlobalTheory
theorem _root_.solution (G : Type v) [Group G] [Finite G]
    (A : Type u) [CommRing A] [MulSemiringAction G A] :
    (IsFreeRingAction G A →
      Module.Finite (FixedPoints.subring A G) A ∧ Algebra.Etale (FixedPoints.subring A G) A ∧
      Module.Projective (FixedPoints.subring A G) A ∧
      Module.FaithfullyFlat (FixedPoints.subring A G) A ∧
      (∀ p : PrimeSpectrum (FixedPoints.subring A G), Module.rankAtStalk A p = Nat.card G) ∧
      (∃ e : A ⊗[FixedPoints.subring A G] A ≃ₐ[A] (G → A),
        ∀ (a b : A) (g : G), e (a ⊗ₜ b) g = a * g • b) ∧
      (SemilinearModule.invariantsFunctor.{max w u} G A).IsEquivalence ∧
      (∀ (M : Type w) [AddCommGroup M] [Module A M] [DistribMulAction G M]
        [SMulDistribClass G A M],
        Function.Bijective ((Representation.ofDistribMulAction
          (FixedPoints.subring A G) G M).invariants.subtype.liftBaseChange A) ∧
        ((Module.Finite (FixedPoints.subring A G)
            (Representation.ofDistribMulAction (FixedPoints.subring A G) G M).invariants ∧
          Module.Projective (FixedPoints.subring A G)
            (Representation.ofDistribMulAction (FixedPoints.subring A G) G M).invariants) ↔
          (Module.Finite A M ∧ Module.Projective A M))) ∧
      ∀ (N : Type w) [AddCommGroup N] [Module (FixedPoints.subring A G) N],
        Function.Bijective (FreeQuotient.toInvariantsTensor G A (FixedPoints.subring A G) N)) ∧
    ∀ (M : Type w) [AddCommGroup M] [Module A M] [DistribMulAction G M]
      [SMulDistribClass G A M] [Module.Finite A M] [Module.Projective A M],
      (∀ P : Ideal A, P.IsMaximal → (Nat.card (P.inertia G) : A) ∉ P) →
      (∀ P : Ideal A, P.IsMaximal → ∀ g ∈ P.inertia G, ∀ m : M,
        g • m - m ∈ P • (⊤ : Submodule A M)) →
      Function.Bijective ((Representation.ofDistribMulAction
        (FixedPoints.subring A G) G M).invariants.subtype.liftBaseChange A) ∧
      Module.Finite (FixedPoints.subring A G)
        (Representation.ofDistribMulAction (FixedPoints.subring A G) G M).invariants ∧
      Module.Projective (FixedPoints.subring A G)
        (Representation.ofDistribMulAction (FixedPoints.subring A G) G M).invariants := by
  refine ⟨fun h ↦ ⟨(FreeQuotient.finite_and_projective _ h).1, FreeQuotient.etale _ h,
    (FreeQuotient.finite_and_projective _ h).2, FreeQuotient.faithfullyFlat _ h,
    FreeQuotient.rankAtStalk_eq_card _ h,
    ⟨FreeQuotient.galoisEquiv _ h, FreeQuotient.galoisEquiv_tmul _ h⟩,
    SemilinearModule.invariantsFunctor_isEquivalence.{w} h,
    fun M _ _ _ _ ↦ ⟨FreeQuotient.bijective_liftBaseChange_of_isBaseChange _ M
      (FreeQuotient.isBaseChange_invariants _ M h),
      FreeQuotient.finite_projective_invariants_iff _ M h⟩,
    fun N _ _ ↦ FreeQuotient.bijective_toInvariantsTensor _ N h⟩, fun M _ _ _ _ _ _ h hM ↦ ?_⟩
  obtain ⟨h1, h2⟩ := FreeQuotient.tame_descent (FixedPoints.subring A G) M h hM
  exact ⟨FreeQuotient.bijective_liftBaseChange_of_isBaseChange _ M h1, h2⟩
end GlobalTheory
