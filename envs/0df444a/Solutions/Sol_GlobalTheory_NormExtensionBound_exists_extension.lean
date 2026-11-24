-- Prove2me | solution 1 for GlobalTheory.NormExtensionBound.exists_extension
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T19:14:46.606098+00:00
-- url     : https://prove2.me/submissions/5d1d539e-e4c4-4575-a5c0-54026f91e7d1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormLeOneOfExtension

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.NormExtensionBound
open scoped Pointwise
namespace GlobalTheory.NormExtensionBound
theorem _root_.solution {A B K : Type} [CommRing A] [CommRing B] [Field K] [IsAlgClosed K]
    [Algebra A B] [Algebra.IsIntegral A B] (hinj : Function.Injective (algebraMap A B))
    (ev : A →+* K) : ∃ ev' : B →+* K, ∀ a, ev' (algebraMap A B a) = ev a := by
  haveI hP : (RingHom.ker ev).IsPrime := RingHom.ker_isPrime ev
  obtain ⟨Q, -, hQ, hQP⟩ := Ideal.exists_ideal_over_prime_of_isIntegral (S := B)
    (RingHom.ker ev) ⊥ (by
      intro a ha
      have : a = 0 := hinj (by simpa using ha)
      simp [this])
  haveI : Q.LiesOver (RingHom.ker ev) := ⟨hQP.symm⟩
  letI : Algebra (A ⧸ RingHom.ker ev) K := (RingHom.kerLift ev).toAlgebra
  haveI : FaithfulSMul (A ⧸ RingHom.ker ev) K :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 (RingHom.kerLift_injective ev)
  haveI : Algebra.IsIntegral (A ⧸ RingHom.ker ev) (B ⧸ Q) := inferInstance
  haveI : FaithfulSMul (A ⧸ RingHom.ker ev) (B ⧸ Q) := inferInstance
  haveI : Module.IsTorsionFree (A ⧸ RingHom.ker ev) (B ⧸ Q) :=
    Module.IsTorsionFree.of_smul_eq_zero fun r x h => by
      rw [Algebra.smul_def, mul_eq_zero] at h
      exact h.imp_left fun h => FaithfulSMul.algebraMap_injective _ (B ⧸ Q) (by rw [h, map_zero])
  haveI : Module.IsTorsionFree (A ⧸ RingHom.ker ev) K :=
    Module.IsTorsionFree.of_smul_eq_zero fun r x h => by
      rw [Algebra.smul_def, mul_eq_zero] at h
      exact h.imp_left fun h => FaithfulSMul.algebraMap_injective _ K (by rw [h, map_zero])
  haveI : Algebra.IsAlgebraic (A ⧸ RingHom.ker ev) (B ⧸ Q) :=
    ⟨fun x => (Algebra.IsIntegral.isIntegral x).isAlgebraic⟩
  let f : (B ⧸ Q) →ₐ[A ⧸ RingHom.ker ev] K := IsAlgClosed.lift
  refine ⟨f.toRingHom.comp (Ideal.Quotient.mk Q), fun a => ?_⟩
  have h := f.commutes (Ideal.Quotient.mk _ a)
  exact h
end GlobalTheory.NormExtensionBound
