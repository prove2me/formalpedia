-- Prove2me | solution 1 for GlobalTheory.T.adelicCompletion_fractionalIdeal_properties_alt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T12:56:32.775938+00:00
-- url     : https://prove2.me/submissions/3b81c522-d01d-4a64-b736-c84584e4729a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_AdelicCompletionFractionalIdealProperties
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_Hat1
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_AdelicCompletionFractionalIdealPropertiesStatement
import Theorems.Thm_GlobalTheory_AdLat_adelicCompletion_fractionalIdeal_properties


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.AdLat
open scoped TensorProduct Matrix nonZeroDivisors
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E], (∀ I J : FractionalIdeal (𝓞 E)⁰ E, ∀ x ∈ hat1 F (I : Set E), ∀ y ∈ hat1 F (J : Set E), x * y ∈ hat1 F ((I * J : FractionalIdeal (𝓞 E)⁰ E) : Set E)) ∧ (∀ (I : FractionalIdeal (𝓞 E)⁰ E) (x : E), (1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] x ∈ hat1 F (I : Set E) ↔ x ∈ I) ∧ (∀ (I J : FractionalIdeal (𝓞 E)⁰ E) (z : RA F E), I ≠ 0 → (∀ x ∈ I, z * ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] x) ∈ hat1 F (J : Set E)) → z ∈ hat1 F ((J * I⁻¹ : FractionalIdeal (𝓞 E)⁰ E) : Set E)) ∧ ∀ (c : E ≃ₐ[F] E) (I I' : FractionalIdeal (𝓞 E)⁰ E), (∀ x ∈ I, c x ∈ I') → ∀ z ∈ hat1 F (I : Set E), sg (FiniteAdeleRing (𝓞 F) F) c z ∈ hat1 F (I' : Set E) := by
  first | exact @GlobalTheory.AdLat.adelicCompletion_fractionalIdeal_properties | exact GlobalTheory.AdLat.adelicCompletion_fractionalIdeal_properties | (intros; apply GlobalTheory.AdLat.adelicCompletion_fractionalIdeal_properties <;> assumption)
end _root_.GlobalTheory.T
