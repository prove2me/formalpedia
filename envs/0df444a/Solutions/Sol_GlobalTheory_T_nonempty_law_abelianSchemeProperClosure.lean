-- Prove2me | solution 1 for GlobalTheory.T.nonempty_law_abelianSchemeProperClosure
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T14:58:31.413641+00:00
-- url     : https://prove2.me/submissions/7f4f5898-706b-493e-ab7b-23fb10e9e573

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_NonemptyLawAbelianSchemeProperClosure
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_IsNormalSchemeSp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_NonemptyLawAbelianSchemeProperClosureStatement
import Theorems.Thm_GlobalTheory_ZJ_Core_nonempty_law


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
theorem _root_.solution : ∀ C : Core, SmoothOfRelativeDimension C.g C.GG.hom → C.TestCart → (∃ m : C.GG ⊗ C.GG ⟶ C.GG, ∀ φ₂ : (C.A ⊗ C.A).left ⟶ (C.GG ⊗ C.GG).left, IsSquare C.a φ₂ → φ₂ ≫ m.left = (μ[C.A]).left ≫ C.a) → (∃ i : C.GG ⟶ C.GG, C.a ≫ i.left = (ι[C.A]).left ≫ C.a) → Nonempty C.Law := by
  first | exact @GlobalTheory.ZJ.Core.nonempty_law | exact GlobalTheory.ZJ.Core.nonempty_law | (intros; apply GlobalTheory.ZJ.Core.nonempty_law <;> assumption)
end _root_.GlobalTheory.T
