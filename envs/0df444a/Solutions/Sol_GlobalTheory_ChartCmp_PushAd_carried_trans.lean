-- Prove2me | solution 1 for GlobalTheory.ChartCmp.PushAd.carried_trans
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T14:09:55.600404+00:00
-- url     : https://prove2.me/submissions/e7a2148d-d3d9-4fa8-9dbf-9c65ca235e3a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_AdditionLawSecondIdentity
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_ExistsGroupIsoCubicalIsoOfTripleMapId
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ThetaSwapFirstTwo
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_AdjointnessSeriesTransportFrames
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_HasGen_pull
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_isGen_iff


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.TB (dLin transF IsInvPair dAct)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ChartCmp
open GlobalTheory GlobalTheory.ChartCmp GlobalTheory.ChartCmp.PushAd
variable {X X' Y : Scheme.{0}} {L' : LB X'} {L : LB X} {F : X' ⟶ X} (w : LB.Iso L' (L.pull F))
  {K : Type} [Fintype K] {φ : K → (Y ⟶ X')} {ε : K → ℤ}
namespace GlobalTheory.ChartCmp.PushAd
theorem _root_.solution (hw : w.IsGen) {g : LB.Gen (LB.LinComb L' φ ε)} (hg : g.IsGen) {Z : Scheme.{0}} (r : Z ⟶ Y)
    (z : Z) (p p' : K → L.ι) (q q' : K → L'.ι) (hp : r z ∈ LB.wchart L (fun k => φ k ≫ F) p)
    (hp' : r z ∈ LB.wchart L (fun k => φ k ≫ F) p') (hq : r z ∈ LB.wchart L' φ q) (hq' : r z ∈ LB.wchart L' φ q') :
    (∏ k, gw w (r ≫ φ k) z (p k) (q k) ^ ε k) * gm r z (LB.wchart L' φ q) (g.s q) =
      trF (fun k => φ k ≫ F) ε r z p p' *
        ((∏ k, gw w (r ≫ φ k) z (p' k) (q' k) ^ ε k) * gm r z (LB.wchart L' φ q') (g.s q')) := by
  rw [gen_trans hg r z hq hq', ← _root_.mul_assoc, ← _root_.mul_assoc, trF, trF, ← Finset.prod_mul_distrib,
    ← Finset.prod_mul_distrib]
  refine congrArg (· * _) (Finset.prod_congr rfl fun k _ => ?_)
  rw [← mul_zpow, ← mul_zpow, (isGen_iff w).1 hw Z (r ≫ φ k) z (p k) (p' k) (q k) (q' k) (Set.mem_iInter.1 hp k)
    (Set.mem_iInter.1 hp' k) (Set.mem_iInter.1 hq k) (Set.mem_iInter.1 hq' k), Category.assoc, mul_right_comm _ (gw _ _ _ _ _),
    inv_mul_cancel_right]
end GlobalTheory.ChartCmp.PushAd
