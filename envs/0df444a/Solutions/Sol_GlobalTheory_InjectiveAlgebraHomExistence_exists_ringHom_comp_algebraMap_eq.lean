-- Prove2me | solution 1 for GlobalTheory.InjectiveAlgebraHomExistence.exists_ringHom_comp_algebraMap_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T18:03:06.640629+00:00
-- url     : https://prove2.me/submissions/ce0b0d87-94b9-47ac-bfbd-bc80887038c5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsRingHomCompAlgebraMapEq
import Theorems.Thm_GlobalTheory_InjectiveAlgebraHomExistence_exists_algHom_of_injective

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u_1 u_2 u_3
open GlobalTheory GlobalTheory.InjectiveAlgebraHomExistence
namespace GlobalTheory.InjectiveAlgebraHomExistence
theorem _root_.solution {R : Type u_1} {S : Type u_2} {K : Type u_3}
    [CommRing R] [CommRing S] [Field K] [IsAlgClosed K] [Algebra R S] [Algebra.IsIntegral R S]
    (hinj : Function.Injective (algebraMap R S)) (ψ : R →+* K) :
    ∃ x : S →+* K, x.comp (algebraMap R S) = ψ := by
  have hp : (RingHom.ker ψ).IsPrime := RingHom.ker_isPrime ψ
  obtain ⟨Q, -, hQ, hQp⟩ := Ideal.exists_ideal_over_prime_of_isIntegral (S := S)
    (RingHom.ker ψ) ⊥ (by
      intro r hr
      have h0 : algebraMap R S r = 0 := by simpa using hr
      have : r = 0 := hinj (by simpa using h0)
      simp [this])
  let f : R ⧸ RingHom.ker ψ →+* S ⧸ Q := Ideal.quotientMap Q (algebraMap R S) hQp.ge
  have hf : Function.Injective f := Ideal.quotientMap_injective' hQp.le
  letI : Algebra (R ⧸ RingHom.ker ψ) (S ⧸ Q) := f.toAlgebra
  letI : Algebra (R ⧸ RingHom.ker ψ) K := (RingHom.kerLift ψ).toAlgebra
  haveI : Algebra.IsIntegral (R ⧸ RingHom.ker ψ) (S ⧸ Q) := by
    constructor
    intro y
    obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective y
    obtain ⟨P, hP, hs⟩ := Algebra.IsIntegral.isIntegral (R := R) s
    refine ⟨P.map (Ideal.Quotient.mk _), hP.map _, ?_⟩
    have hc : (algebraMap (R ⧸ RingHom.ker ψ) (S ⧸ Q)).comp (Ideal.Quotient.mk _)
        = (Ideal.Quotient.mk Q).comp (algebraMap R S) := by
      ext r
      rfl
    rw [Polynomial.eval₂_map, hc, ← Polynomial.hom_eval₂, hs, map_zero]
  obtain ⟨g⟩ : Nonempty ((S ⧸ Q) →ₐ[R ⧸ RingHom.ker ψ] K) :=
    exists_algHom_of_injective hf (RingHom.kerLift_injective ψ)
  refine ⟨(g : (S ⧸ Q) →+* K).comp (Ideal.Quotient.mk Q), ?_⟩
  ext r
  have := g.commutes (Ideal.Quotient.mk _ r)
  exact this
end GlobalTheory.InjectiveAlgebraHomExistence
