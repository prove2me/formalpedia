-- Prove2me | solution 1 for GlobalTheory.ValuationExtensionExistence.exists_extension
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:10:33.569824+00:00
-- url     : https://prove2.me/submissions/9076e589-17c7-40a1-a8d2-fda321de7bc9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ImportsFurtherLast

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.ValuationExtensionExistence
namespace GlobalTheory.ValuationExtensionExistence
theorem _root_.solution {V R K : Type} [CommRing V] [CommRing R] [IsDomain R] [Field K]
    [IsAlgClosed K] [Algebra V R] [Algebra.IsIntegral V R] [FaithfulSMul V R] (ev : V →+* K) :
    ∃ ev₁ : R →+* K, ev₁.comp (algebraMap V R) = ev := by
  classical

  have : (RingHom.ker ev).IsPrime := RingHom.ker_isPrime ev
  obtain ⟨Q, -, hQ, hQp⟩ := Ideal.exists_ideal_over_prime_of_isIntegral (S := R) (RingHom.ker ev) ⊥ (by
    rw [Ideal.comap_bot_of_injective _ (FaithfulSMul.algebraMap_injective V R)]
    exact bot_le)
  have := hQ
  have : Q.LiesOver (RingHom.ker ev) := ⟨hQp.symm⟩

  let : Algebra (V ⧸ RingHom.ker ev) K := (RingHom.kerLift ev).toAlgebra
  have : Module.IsTorsionFree (V ⧸ RingHom.ker ev) K :=
    Module.isTorsionFree_iff_algebraMap_injective.2 (RingHom.kerLift_injective ev)
  have : Module.IsTorsionFree (V ⧸ RingHom.ker ev) (R ⧸ Q) :=
    Module.isTorsionFree_iff_algebraMap_injective.2 (FaithfulSMul.algebraMap_injective _ _)
  have : Algebra.IsIntegral (V ⧸ RingHom.ker ev) (R ⧸ Q) :=
    Ideal.Quotient.algebra_isIntegral_of_liesOver Q (RingHom.ker ev)
  have : Algebra.IsAlgebraic (V ⧸ RingHom.ker ev) (R ⧸ Q) := Algebra.IsIntegral.isAlgebraic
  let f : R ⧸ Q →ₐ[V ⧸ RingHom.ker ev] K := IsAlgClosed.lift
  refine ⟨(f : R ⧸ Q →+* K).comp (Ideal.Quotient.mk Q), ?_⟩
  ext v
  have h := f.commutes (Ideal.Quotient.mk (RingHom.ker ev) v)
  rw [Ideal.Quotient.algebraMap_mk_of_liesOver] at h
  exact h.trans (RingHom.kerLift_mk ev v)
end GlobalTheory.ValuationExtensionExistence
