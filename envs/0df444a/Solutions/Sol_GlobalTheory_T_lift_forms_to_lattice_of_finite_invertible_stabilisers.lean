-- Prove2me | solution 1 for GlobalTheory.T.lift_forms_to_lattice_of_finite_invertible_stabilisers
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T18:21:15.118519+00:00
-- url     : https://prove2.me/submissions/46db89c0-f909-4211-97cc-0f53e890ef92

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LiftFormsToLatticeOfFiniteInvertibleStabilisers
import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LiftFormsToLatticeOfFiniteInvertibleStabilisersStatement
import Theorems.Thm_GlobalTheory_lift_forms_of_card_isUnit


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (O : Type) [CommRing O] (G : Type) [Group G] (Γ K : Subgroup G) (B Q : Type) [AddCommGroup B] [Module O B] [AddCommGroup Q] [Module O Q] (ρ : Representation O K B) (π : B →ₗ[O] Q), Function.Surjective π → (∀ κ x, π x = 0 → π (ρ κ x) = 0) → (∀ g : G, Finite {γ : Γ // g⁻¹ * (γ : G) * g ∈ K} ∧ IsUnit ((Nat.card {γ : Γ // g⁻¹ * (γ : G) * g ∈ K} : ℕ) : O)) → ∀ f : G → Q, (∀ (γ : Γ) (g : G) (κ : K) (y : B), f g = π y → f ((γ : G) * g * κ) = π (ρ κ⁻¹ y)) → ∃ F ∈ Formalism.UG.AMFK O Γ K ρ, ∀ g, π (F g) = f g := by
  first | exact @GlobalTheory.lift_forms_of_card_isUnit | exact GlobalTheory.lift_forms_of_card_isUnit | (intros; apply GlobalTheory.lift_forms_of_card_isUnit <;> assumption)
end _root_.GlobalTheory.T
