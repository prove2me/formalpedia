-- Prove2me | solution 1 for GlobalTheory.T.awayMap_bijective_of_injective_of_range_eq_subalgebra
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:33:59.633973+00:00
-- url     : https://prove2.me/submissions/8207139c-133d-4704-afeb-252d2b20a82b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AwayMapBijectiveOfRangeEqSubalgebra
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AwayMapBijectiveOfRangeEqSubalgebraStatement
import Theorems.Thm_GlobalTheory_awayMap_bijective_of_range_eq_subalgebra


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits Scheme.AffineZariskiSite
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (R A B : Type) [CommRing R] [CommRing A] [CommRing B] [Algebra R B] (C : Subalgebra R B) (φ : A →+* B), Function.Injective φ → ∀ (_ : ∀ x, x ∈ C ↔ ∃ y, φ y = x) (a : A) (b : B), φ a = b → (∀ hb : b ∈ C, Function.Bijective (Localization.awayMap C.val.toRingHom (⟨b, hb⟩ : C))) → Function.Bijective (Localization.awayMap φ a) := by
  first | exact @GlobalTheory.awayMap_bijective_of_range_eq_subalgebra | exact GlobalTheory.awayMap_bijective_of_range_eq_subalgebra | (intros; apply GlobalTheory.awayMap_bijective_of_range_eq_subalgebra <;> assumption)
end _root_.GlobalTheory.T
