-- Prove2me | solution 1 for GlobalTheory.T.eq_of_agree_on_affineOpen_generators
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T18:16:22.329333+00:00
-- url     : https://prove2.me/submissions/b2cc801d-c813-4e65-9ccf-b8ddbc63a2b6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_EqOfAgreeOnAffineOpenGenerators
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_EqOfAgreeOnAffineOpenGeneratorsStatement
import Theorems.Thm_GlobalTheory_eq_of_agree_on_generators


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (R : Type) [CommRing R] (X W : Scheme.{0}) (sm : X ⟶ Spec (CommRingCat.of R)) (N : X.Opens), IsAffineOpen N → ∀ (m : ℕ) (r : Fin m → Γ(X, N)), (∀ g : Γ(X, N), ∃ P Q : MvPolynomial (Fin m) R, IsUnit (MvPolynomial.eval₂ (GlobalTheory.AbLaw.cst sm N) r Q) ∧ g * MvPolynomial.eval₂ (GlobalTheory.AbLaw.cst sm N) r Q = MvPolynomial.eval₂ (GlobalTheory.AbLaw.cst sm N) r P) → ∀ (a b : W ⟶ X), a ≫ sm = b ≫ sm → ∀ (ha : ⊤ ≤ a ⁻¹ᵁ N) (hb : ⊤ ≤ b ⁻¹ᵁ N), (∀ l, (W.presheaf.map (homOfLE ha).op).hom ((a.app N).hom (r l)) = (W.presheaf.map (homOfLE hb).op).hom ((b.app N).hom (r l))) → a = b := by
  first | exact @GlobalTheory.eq_of_agree_on_generators | exact GlobalTheory.eq_of_agree_on_generators | (intros; apply GlobalTheory.eq_of_agree_on_generators <;> assumption)
end _root_.GlobalTheory.T
