-- Prove2me | solution 1 for GlobalTheory.DegActCheck.pt_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:41:00.922705+00:00
-- url     : https://prove2.me/submissions/a880ef78-3021-4cda-85a2-295aec787a62

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_ModuliSurvey_PsiUnitOnIffInterior

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.DegActCheck
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
variable {R : Type} [CommRing R] [IsDomain R]
variable {O : Type} [CommRing O] [StarRing O] (D : Out.DegPre R) [Module O D.X] (oa : D.OAct O) (w : O) (y : D.X)
namespace GlobalTheory.DegActCheck
theorem _root_.solution : D.xK y ≫ (toUnit D.P.A ≫ η[D.P.A]).left = (toUnit (Out.TK R)).left ≫ eSec D.P.A := by
  show (toUnit (Out.TK R) ≫ D.c y).left ≫ _ = (toUnit (Out.TK R)).left ≫ (η[D.P.A]).left
  rw [← Over.comp_left, ← Over.comp_left, ← Category.assoc, comp_toUnit]
end GlobalTheory.DegActCheck
