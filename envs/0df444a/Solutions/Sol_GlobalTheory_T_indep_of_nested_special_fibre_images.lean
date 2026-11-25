-- Prove2me | solution 1 for GlobalTheory.T.indep_of_nested_special_fibre_images
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T04:14:52.534475+00:00
-- url     : https://prove2.me/submissions/40eeb37e-1cd3-4a25-9259-6a81bfbd299c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_IndepOfNestedSpecialFibreImages
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_IsNormalSchemeSp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_IndepOfNestedSpecialFibreImagesStatement
import Theorems.Thm_GlobalTheory_ZJ_Core_indep_of_special_fibres


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
open GlobalTheory.ZJ
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ C : Core, C.HasTests → (∀ (p : ℕ) [Fact p.Prime] (y y' : Sp (OO p) ⟶ C.Z), C.Cl y → C.Cl y' → rPt p ≫ y = rPt p ≫ y' → ∃ (τ : C.Test y) (τ' : C.Test y'), ∀ c : Sp (kb p) ⟶ τ.H.left, c ≫ τ.H.hom = rPt p ≫ spMap τ.j → ∃ c' : Sp (kb p) ⟶ τ'.H.left, c' ≫ τ'.H.hom = rPt p ≫ spMap τ'.j ∧ c' ≫ τ'.f = c ≫ τ.f) → C.Indep := by
  first | exact @GlobalTheory.ZJ.Core.indep_of_special_fibres | exact GlobalTheory.ZJ.Core.indep_of_special_fibres | (intros; apply GlobalTheory.ZJ.Core.indep_of_special_fibres <;> assumption)
end _root_.GlobalTheory.T
