-- Prove2me | solution 1 for GlobalTheory.SquareTower.tower
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T21:10:55.858833+00:00
-- url     : https://prove2.me/submissions/58ea50e5-d92f-4193-986b-4cf7ce586caf

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsSquarePresentationOfTower
import Theorems.Thm_GlobalTheory_SquareTower_square_of_pres

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
open GlobalTheory GlobalTheory.SquareTower
open MvPolynomial
namespace GlobalTheory.SquareTower
theorem _root_.solution : ∀ (k B A : Type) [CommRing k] [CommRing B] [CommRing A] [Algebra k B] [Algebra k A] [Algebra B A] [IsScalarTower k B A], (∃ (s : ℕ) (φ : MvPolynomial (Fin s) k →ₐ[k] B) (g : Fin s → MvPolynomial (Fin s) k), Function.Surjective φ ∧ RingHom.ker φ = Ideal.span (Set.range g)) → (∃ (s : ℕ) (φ : MvPolynomial (Fin s) B →ₐ[B] A) (g : Fin s → MvPolynomial (Fin s) B), Function.Surjective φ ∧ RingHom.ker φ = Ideal.span (Set.range g)) → (∃ (s : ℕ) (φ : MvPolynomial (Fin s) k →ₐ[k] A) (g : Fin s → MvPolynomial (Fin s) k), Function.Surjective φ ∧ RingHom.ker φ = Ideal.span (Set.range g)) := by
  intro k B A _ _ _ _ _ _ _
  rintro ⟨t, φ, g, hφ, hg⟩ ⟨d, ψ, h, hψ, hh⟩
  let P := presOf φ g hφ hg
  let Q := presOf ψ h hψ hh
  exact square_of_pres (Q.comp P) finSumFinEquiv.symm finSumFinEquiv.symm
end GlobalTheory.SquareTower
