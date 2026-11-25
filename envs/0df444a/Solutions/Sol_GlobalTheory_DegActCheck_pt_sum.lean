-- Prove2me | solution 1 for GlobalTheory.DegActCheck.pt_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:55:15.078207+00:00
-- url     : https://prove2.me/submissions/651e9275-b27a-4064-9f57-cf8131bc3029

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
theorem _root_.solution : D.xK y ≫ (padd D.P.A (𝟙 _) (oa.onB.act w)).left = D.xK (y + w • y) := by
  show (toUnit (Out.TK R) ≫ D.c y).left ≫ _ = (toUnit (Out.TK R) ≫ D.c (y + w • y)).left
  rw [D.c_add, oa.c_lin, ← Over.comp_left]
  congr 1
  simp only [padd, Category.assoc, comp_lift_assoc, Category.comp_id]
end GlobalTheory.DegActCheck
