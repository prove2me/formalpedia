-- Prove2me | solution 1 for GlobalTheory.T.exists_generic_functionField_point
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T21:08:09.341835+00:00
-- url     : https://prove2.me/submissions/39d88784-36f6-4c7c-9ea5-1e80aa153d7c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsGenericFunctionFieldPoint
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_IsUnitEv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsGenericFunctionFieldPointStatement
import Theorems.Thm_GlobalTheory_SS_WtRat_exists_generic_field_point


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (Y : Scheme.{0}) [IsIntegral Y], ∃ (F : Type) (_ : Field F) (g : Sp F ⟶ Y) (hg : ∀ V : Y.Opens, (V : Set Y).Nonempty → ⊤ ≤ g ⁻¹ᵁ V), (∀ (V : Y.Opens) (hV : (V : Set Y).Nonempty), Function.Injective (WtRat.ev g V (hg V hV))) ∧ (∀ τ : Y ≅ Y, ∃ σ : F →+* F, spMap σ ≫ g = g ≫ τ.hom) ∧ ∀ U : Y.Opens, (U : Set Y).Nonempty → ∀ (I : Type) [Fintype I] (x : I → F), ∃ (U' : Y.Opens) (hU' : (U' : Set Y).Nonempty) (s : I → Γ(Y, U')), U' ≤ U ∧ ∀ j, WtRat.ev g U' (hg U' hU') (s j) = x j ∧ (x j ≠ 0 → IsUnit (s j)) := by
  first | exact @GlobalTheory.SS.WtRat.exists_generic_field_point | exact GlobalTheory.SS.WtRat.exists_generic_field_point | (intros; apply GlobalTheory.SS.WtRat.exists_generic_field_point <;> assumption)
end _root_.GlobalTheory.T
