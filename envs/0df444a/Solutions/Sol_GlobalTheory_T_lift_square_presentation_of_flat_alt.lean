-- Prove2me | solution 1 for GlobalTheory.T.lift_square_presentation_of_flat_alt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:43:14.33201+00:00
-- url     : https://prove2.me/submissions/fece4a62-5d61-49f5-9f69-f97b06e9c07d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LiftSquarePresentationOfFlat
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LiftSquarePresentationOfFlatStatement
import Theorems.Thm_GlobalTheory_lift_square_presentation_of_flat


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (O B A k H σ : Type) [CommRing O] [IsLocalRing O] [CommRing B] [CommRing A] [Algebra O B] [Algebra O A] [Algebra B A] [IsScalarTower O B A] [Module.Flat B A] [Field k] [CommRing H] [Algebra k H] [Fintype σ] (ε : A →ₐ[O] O) (π : O →+* k) (ρ : A →+* H) (εH : H →ₐ[k] k) (x : σ → A), Function.Surjective π → RingHom.ker π = IsLocalRing.maximalIdeal O → (∀ c : O, ρ (algebraMap O A c) = algebraMap k H (π c)) → (∀ a, εH (ρ a) = π (ε a)) → RingHom.ker ρ = (RingHom.ker (π.comp ((ε : A →+* O).comp (algebraMap B A)))).map (algebraMap B A) → Function.Surjective (MvPolynomial.aeval x : MvPolynomial σ B →ₐ[B] A) → (RingHom.ker (MvPolynomial.aeval x : MvPolynomial σ B →ₐ[B] A)).FG → ∀ g : σ → MvPolynomial σ k, (∀ i, MvPolynomial.aeval (fun j => ρ (x j)) (g i) = 0) → RingHom.ker (MvPolynomial.aeval (fun j => ρ (x j)) : MvPolynomial σ k →ₐ[k] H) ≤ Ideal.span (Set.range g) ⊔ RingHom.ker (εH.comp (MvPolynomial.aeval (fun j => ρ (x j)) : MvPolynomial σ k →ₐ[k] H)) * RingHom.ker (MvPolynomial.aeval (fun j => ρ (x j)) : MvPolynomial σ k →ₐ[k] H) → ∃ f : σ → MvPolynomial σ B, (∀ i, MvPolynomial.aeval x (f i) = 0) ∧ RingHom.ker (MvPolynomial.aeval x : MvPolynomial σ B →ₐ[B] A) ≤ Ideal.span (Set.range f) ⊔ (RingHom.ker ε).comap (MvPolynomial.aeval x : MvPolynomial σ B →ₐ[B] A) * RingHom.ker (MvPolynomial.aeval x : MvPolynomial σ B →ₐ[B] A) := by
  first | exact @GlobalTheory.lift_square_presentation_of_flat | exact GlobalTheory.lift_square_presentation_of_flat | (intros; apply GlobalTheory.lift_square_presentation_of_flat <;> assumption)
end _root_.GlobalTheory.T
