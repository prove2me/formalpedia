-- Prove2me | solution 1 for GlobalTheory.T.existsUnique_section_of_locally_given_values
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:05:56.167804+00:00
-- url     : https://prove2.me/submissions/4feaa673-5201-4c7f-9b7f-bc05ee7505b5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsUniqueSectionOfLocallyRegular
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsSymm
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsUniqueSectionOfLocallyRegularStatement
import Theorems.Thm_GlobalTheory_existsUnique_section_of_locally_regular


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
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (P₀ : Out.PolAV (Sp ℂ)) (u : HolUnif P₀.A P₀.L P₀.g) (Hm : Matrix (Fin P₀.g) (Fin P₀.g) ℂ) (χ : u.Λ → ℂ), GoodU u Hm χ → ∀ (O : P₀.A.left.Opens) (h : (Fin P₀.g → ℂ) → ℂ), (∀ z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ O → ∃ (O' : P₀.A.left.Opens) (a : Γ(P₀.A.left, O')), O' ≤ O ∧ ⊤ ≤ (u.ex z).left ⁻¹ᵁ O' ∧ ∀ z', ⊤ ≤ (u.ex z').left ⁻¹ᵁ O' → valAt' (u.ex z').left O' a = h z') → ∃! a : Γ(P₀.A.left, O), ∀ z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ O → valAt' (u.ex z).left O a = h z := by
  first | exact @GlobalTheory.existsUnique_section_of_locally_regular | exact GlobalTheory.existsUnique_section_of_locally_regular | (intros; apply GlobalTheory.existsUnique_section_of_locally_regular <;> assumption)
end _root_.GlobalTheory.T
