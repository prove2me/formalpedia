-- Prove2me | solution 1 for GlobalTheory.TorusTranslate.translate_comp_q
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T03:06:28.872797+00:00
-- url     : https://prove2.me/submissions/9a19c0e4-f9ae-4d96-a3de-e4837de02860

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PullChartIsLB
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsSplitTorusPointsMulEquiv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsPointTranslatePure
import Theorems.Thm_GlobalTheory_TorusTranslate_torus_comp_q

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
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra
open GlobalTheory GlobalTheory.TorusTranslate
variable {S : Scheme.{0}} {E : SplitExt S} {G : Over S} [GrpObj G] (D : E.GtDatum G) {Z : Over S}
namespace GlobalTheory.TorusTranslate
theorem _root_.solution (τ : Z ⟶ splitTorus S E.X) (x : Z ⟶ G) :
    ((τ ≫ D.i) * x).left ≫ D.q.left = x.left ≫ D.q.left := by
  have := D.q_hom
  rw [← Over.comp_left, ← Over.comp_left, MonObj.mul_comp, torus_comp_q, _root_.one_mul]
end GlobalTheory.TorusTranslate
