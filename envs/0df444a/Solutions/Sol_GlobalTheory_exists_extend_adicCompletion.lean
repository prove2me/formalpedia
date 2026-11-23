-- Prove2me | solution 1 for GlobalTheory.exists_extend_adicCompletion
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:37:13.747804+00:00
-- url     : https://prove2.me/submissions/9259e67e-8059-4acb-abd2-838a2d696729

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsUniqueFactorCompletedStalkOfMap
import Theorems.Thm_P2M_GlobalTheory_factorPow_eval__9207485a8623
import Theorems.Thm_GlobalTheory_pow_mul_le_comap_pow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry IsLocalRing
universe u
open GlobalTheory
variable {A R : Type*} [CommRing A] [CommRing R]
namespace GlobalTheory
theorem _root_.solution (φ : A →+* R) (J : Ideal A) (I : Ideal R)
    [IsAdicComplete I R] {k : ℕ} (hk : J.map φ ^ k ≤ I) :
    ∃ ψ : AdicCompletion J A →+* R, ψ.comp (algebraMap A (AdicCompletion J A)) = φ ∧
      ∀ (n : ℕ) (x : AdicCompletion J A) (a : A),
        AdicCompletion.evalₐ J (k * n) x = Ideal.Quotient.mk _ a → ψ x - φ a ∈ I ^ n := by
  let f : (n : ℕ) → AdicCompletion J A →+* R ⧸ I ^ n := fun n =>
    (Ideal.quotientMap (I ^ n) φ (pow_mul_le_comap_pow φ hk n)).comp
      (AdicCompletion.evalₐ J (k * n)).toRingHom
  have hfa : ∀ n x a, AdicCompletion.evalₐ J (k * n) x = Ideal.Quotient.mk _ a →
      f n x = Ideal.Quotient.mk _ (φ a) := by
    intro n x a h
    change Ideal.quotientMap (I ^ n) φ (pow_mul_le_comap_pow φ hk n) (AdicCompletion.evalₐ J (k * n) x) = _
    rw [h, Ideal.quotientMap_mk]
  have hf : ∀ {m n : ℕ} (hle : m ≤ n), (Ideal.Quotient.factorPow I hle).comp (f n) = f m := by
    intro m n hle
    refine RingHom.ext fun x => ?_
    obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ J (k * n) x)
    have ha' : AdicCompletion.evalₐ J (k * m) x = Ideal.Quotient.mk _ a := by
      rw [← factorPow_evalₐ J (Nat.mul_le_mul_left k hle), ← ha]
      rfl
    rw [RingHom.comp_apply, hfa n x a ha.symm, hfa m x a ha']
    rfl
  have key : ∀ (n : ℕ) (x : AdicCompletion J A) (a : A),
      AdicCompletion.evalₐ J (k * n) x = Ideal.Quotient.mk _ a →
        IsAdicComplete.liftRingHom I f hf x - φ a ∈ I ^ n := by
    intro n x a h
    rw [← Ideal.Quotient.eq, IsAdicComplete.mk_liftRingHom, hfa n x a h]
  refine ⟨IsAdicComplete.liftRingHom I f hf, ?_, key⟩
  apply DFunLike.coe_injective
  apply IsHausdorff.funext' I
  intro n a
  exact Ideal.Quotient.eq.mpr (key n _ a (AdicCompletion.evalₐ_of J _ a))
end GlobalTheory
