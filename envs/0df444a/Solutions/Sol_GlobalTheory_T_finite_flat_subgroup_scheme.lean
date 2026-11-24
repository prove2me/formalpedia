-- Prove2me | solution 1 for GlobalTheory.T.finite_flat_subgroup_scheme
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T21:09:35.033333+00:00
-- url     : https://prove2.me/submissions/27e0a747-77ce-478b-a6d9-3b333b20846f

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_AlgebraProofs_FiniteFlatSubgroupScheme
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_CommutativeAlgebra_IsFinFlatSub
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_AlgebraProofs_FiniteFlatSubgroupSchemeStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_GR_SubGrp_grpObj_of_isFinFlatSub


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.Ar.GR
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (R : Type) [CommRing R] (A : Over (Spec (CommRingCat.of R))) [GrpObj A] (B : Type) [CommRing B] [Algebra R B] (h : sp (R₀ := R) B ⟶ A), IsFinFlatSub A B h → ∃ _ : GrpObj (sp (R₀ := R) B), IsMonHom h ∧ Mono h := by
  first | exact @GlobalTheory.CompanionTheory.Ar.GR.SubGrp.grpObj_of_isFinFlatSub | exact GlobalTheory.CompanionTheory.Ar.GR.SubGrp.grpObj_of_isFinFlatSub | (intros; apply GlobalTheory.CompanionTheory.Ar.GR.SubGrp.grpObj_of_isFinFlatSub <;> assumption)
end _root_.GlobalTheory.T
