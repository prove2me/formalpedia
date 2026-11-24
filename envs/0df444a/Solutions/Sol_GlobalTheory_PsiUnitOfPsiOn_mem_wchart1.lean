-- Prove2me | solution 1 for GlobalTheory.PsiUnitOfPsiOn.mem_wchart1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T19:38:45.862823+00:00
-- url     : https://prove2.me/submissions/992eafa6-3f00-441b-a260-40bff3839368

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PsiUnitOnOfPsiOn

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Semi CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory GlobalTheory.PsiUnitOfPsiOn
namespace GlobalTheory.PsiUnitOfPsiOn
theorem _root_.solution {Y B : Scheme.{0}} (M : LB B) (φ : Y ⟶ B) (z : Y) (i : M.ι) (hz : φ z ∈ M.U i) :
    z ∈ LB.wchart M (fun _ : PUnit => φ) (fun _ => i) := Set.mem_iInter.2 fun _ => hz
end GlobalTheory.PsiUnitOfPsiOn
