-- Prove2me | solution 1 for GlobalTheory.T.orbit_mass_eq_of_finite_double_cosets
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T09:38:55.332834+00:00
-- url     : https://prove2.me/submissions/3e5e20fa-243e-40a8-a540-8b6ed9070f7e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_OrbitMassEqOfFiniteDoubleCosets
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_OrbitMassEqOfFiniteDoubleCosetsStatement
import Theorems.Thm_GlobalTheory_HL_mass_orbit_eq_of_finite_double_cosets


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.HL
open scoped ENNReal Classical
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ {G : Type} [Group G] (Γ K0 : Subgroup G), (∃ S : Finset G, ∀ g : G, ∃ a ∈ S, ∃ γ ∈ Γ, ∃ κ ∈ K0, g = γ * a * κ) → (∀ a : G, {γ | γ ∈ Γ ∧ a⁻¹ * γ * a ∈ K0}.Finite) → ∃ V0 : ℝ, 0 < V0 ∧ ∀ (X : Type) [MulAction G X] (x : X), K0.relIndex (MulAction.stabilizer G x) ≠ 0 → (MulAction.stabilizer G x).relIndex K0 ≠ 0 → (∑' o : MulAction.orbitRel.Quotient Γ X, if o.out ∈ MulAction.orbit G x then ((((Γ ⊓ MulAction.stabilizer G o.out : Subgroup G) : Set G).encard : ℝ≥0∞))⁻¹ else 0) = ENNReal.ofReal (V0 * invVol K0 (MulAction.stabilizer G x)) := by
  first | exact @GlobalTheory.HL.mass_orbit_eq_of_finite_double_cosets | exact GlobalTheory.HL.mass_orbit_eq_of_finite_double_cosets | (intros; apply GlobalTheory.HL.mass_orbit_eq_of_finite_double_cosets <;> assumption)
end _root_.GlobalTheory.T
