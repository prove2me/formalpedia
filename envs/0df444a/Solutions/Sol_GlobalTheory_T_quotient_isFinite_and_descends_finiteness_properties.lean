-- Prove2me | solution 1 for GlobalTheory.T.quotient_isFinite_and_descends_finiteness_properties
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:37:45.191806+00:00
-- url     : https://prove2.me/submissions/9663fe03-1520-4973-abf2-714b9691c373

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_QuotientIsFiniteLocallyOfFiniteTypeDescend
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RigidSys
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Splits
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GtBaseChangeSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_QuotientIsFiniteLocallyOfFiniteTypeDescendStatement
import Theorems.Thm_GlobalTheory_quotient_isFinite_locallyOfFiniteType_descend


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (Γ : Type) [Group Γ] [Finite Γ] (X X' : Scheme.{0}) (ρ : Γ →* Aut X) (π : X ⟶ X'), (IsAffineHom π ∧ (∀ g, (ρ g).hom ≫ π = π) ∧ ∀ V : X'.Opens, Function.Injective (π.app V).hom ∧ ∀ f : Γ(X, π ⁻¹ᵁ V), (∀ g (h : π ⁻¹ᵁ V ≤ (ρ g).hom ⁻¹ᵁ (π ⁻¹ᵁ V)), ((ρ g).hom.appLE _ _ h).hom f = f) → f ∈ Set.range (π.app V).hom) → ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (s' : X' ⟶ S), LocallyOfFiniteType (π ≫ s') → IsFinite π ∧ LocallyOfFiniteType s' ∧ (QuasiCompact (π ≫ s') → QuasiCompact s') ∧ (IsSeparated (π ≫ s') → IsSeparated s') ∧ (IsProper (π ≫ s') → IsProper s') := by
  first | exact @GlobalTheory.quotient_isFinite_locallyOfFiniteType_descend | exact GlobalTheory.quotient_isFinite_locallyOfFiniteType_descend | (intros; apply GlobalTheory.quotient_isFinite_locallyOfFiniteType_descend <;> assumption)
end _root_.GlobalTheory.T
