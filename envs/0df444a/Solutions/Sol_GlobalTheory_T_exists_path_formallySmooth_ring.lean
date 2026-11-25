-- Prove2me | solution 1 for GlobalTheory.T.exists_path_formallySmooth_ring
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T18:17:01.068807+00:00
-- url     : https://prove2.me/submissions/e1fce005-63f4-49b9-a901-39c2ce9e7c7b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsPathFormallySmoothRing
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsAdmissibleIntegralBasisChangeOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsPathFormallySmoothRingStatement
import Theorems.Thm_GlobalTheory_Nef_exists_path_ring


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped IntermediateField Polynomial RatFunc
open GlobalTheory.Nef
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (A B R : Type) [CommRing A] [CommRing B] [CommRing R] [Algebra ℚ R] (π : B →+* A) (ε : A →+* B) (m : A →+* A) (β : B →+* R) (δ : A →+ R), π.FormallySmooth → ε.comp π = RingHom.id B → m.comp π = π → ε.comp m = ε → (∀ f ∈ RingHom.ker ε, m f - 2 * f ∈ RingHom.ker ε ^ 2) → (∀ f g, δ (f * g) = β (ε f) * δ g + β (ε g) * δ f) → (∀ a, δ (π a) = 0) → ∃ γ : A →+* PowerSeries R, γ.comp π = PowerSeries.C.comp β ∧ PowerSeries.constantCoeff.comp γ = β.comp ε ∧ (∀ f, PowerSeries.coeff 1 (γ f) = δ f) ∧ (PowerSeries.rescale 2).comp γ = γ.comp m := by
  first | exact @GlobalTheory.Nef.exists_path_ring | exact GlobalTheory.Nef.exists_path_ring | (intros; apply GlobalTheory.Nef.exists_path_ring <;> assumption)
end _root_.GlobalTheory.T
