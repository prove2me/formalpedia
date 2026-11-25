-- Prove2me | solution 1 for GlobalTheory.T.exists_stalk_retraction_of_small_lifting
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T18:17:58.075526+00:00
-- url     : https://prove2.me/submissions/dd8cc07c-440a-4e77-948c-573cb8562e9b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsStalkRetractionOfSmallLifting
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsStalkRetractionOfSmallLiftingStatement
import Theorems.Thm_GlobalTheory_SmallLift_exists_retraction


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ {X Y : Scheme.{0}} (f : X ⟶ Y), (∀ (B : Type) [CommRing B] [IsLocalRing B] [IsArtinianRing B] (I : Ideal B), I ≤ IsLocalRing.maximalIdeal B → IsLocalRing.maximalIdeal B * I = ⊥ → ∀ (a : Spec (CommRingCat.of (B ⧸ I)) ⟶ X) (b : Spec (CommRingCat.of B) ⟶ Y), a ≫ f = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ b → ∃ l : Spec (CommRingCat.of B) ⟶ X, Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ l = a ∧ l ≫ f = b) → ∀ (x : X) [IsNoetherianRing (Y.presheaf.stalk (f x))], Function.Surjective (f.residueFieldMap x).hom → ∀ n : ℕ, ∃ ψ : X.presheaf.stalk x →+* Y.presheaf.stalk (f x) ⧸ maximalIdeal (Y.presheaf.stalk (f x)) ^ (n + 1), ψ.comp (f.stalkMap x).hom = Ideal.Quotient.mk _ := by
  first | exact @GlobalTheory.SmallLift.exists_retraction | exact GlobalTheory.SmallLift.exists_retraction | (intros; apply GlobalTheory.SmallLift.exists_retraction <;> assumption)
end _root_.GlobalTheory.T
