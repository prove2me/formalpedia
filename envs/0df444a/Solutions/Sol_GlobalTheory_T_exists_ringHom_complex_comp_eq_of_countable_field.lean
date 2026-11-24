-- Prove2me | solution 1 for GlobalTheory.T.exists_ringHom_complex_comp_eq_of_countable_field
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:18:07.666447+00:00
-- url     : https://prove2.me/submissions/d416d621-ee19-442f-88d2-01f7ed27a426

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsRingHomComplexCompEqOfCountable
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsRingHomComplexCompEqOfCountableStatement
import Theorems.Thm_GlobalTheory_exists_ringHom_complex_comp_eq_of_countable


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
open scoped CategoryTheory.Obj TensorProduct
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (o : Type) [CommRing o] (em : o →+* ℂ) (K₀ : Type) [Field K₀] [CharZero K₀] [Countable K₀] (β : o →+* K₀), IsDedekindDomain o → Algebra.FiniteType ℤ o → Function.Injective em → Countable o ∧ ∃ j : K₀ →+* ℂ, j.comp β = em := by
  first | exact @GlobalTheory.exists_ringHom_complex_comp_eq_of_countable | exact GlobalTheory.exists_ringHom_complex_comp_eq_of_countable | (intros; apply GlobalTheory.exists_ringHom_complex_comp_eq_of_countable <;> assumption)
end _root_.GlobalTheory.T
