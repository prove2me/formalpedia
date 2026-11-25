-- Prove2me | solution 1 for GlobalTheory.PushFirstLaw.val_theta
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T03:12:33.648196+00:00
-- url     : https://prove2.me/submissions/395db054-9cba-49ab-b64f-1cd58d560bb4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_AdditionLawSecondIdentity
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ExistsSecondPartialLaw
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_FirstPartialLawPushAlongTripleMap
import Theorems.Thm_GlobalTheory_PushFirstLaw_val_maps
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_pull
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_res
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_of


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
open GlobalTheory GlobalTheory.PushFirstLaw
variable {S S' : Scheme.{0}} {G' : Over S'} {G : Over S} [GrpObj G'] [IsCommMonObj G'] [GrpObj G] [IsCommMonObj G]
namespace GlobalTheory.PushFirstLaw
theorem _root_.solution (m : CubeMap G' G) {L : LB G.left} {L' : LB G'.left} {w : LB.Iso L' (L.pull m.F)}
    {c : LB.Gen (Theta G L)} {c' : LB.Gen (Theta G' L')}
    (h : LB.Gen.Maps (LB.linCombIso w (thφ G' (x3 G')) thε) c' (m.thetaPull L c))
    {Z : Scheme.{0}} {z : Z} {J : (Z ⟶ G.left) → L.ι} {J' : (Z ⟶ G'.left) → L'.ι} (hJ : Good L z J) (hJ' : Good L' z J')
    (r : Z ⟶ (G3 G').left) :
    val (φ := thφ G (x3 G)) (ε := thε) c (r ≫ m.F3) z J =
      (∏ k, isoVal w z J J' (r ≫ thφ G' (x3 G') k) ^ thε k) * val (φ := thφ G' (x3 G')) (ε := thε) c' r z J' := by
  refine Eq.trans ?_ (val_maps hJ hJ' h r)
  have e : ∀ k : thK, (r ≫ m.F3) ≫ thφ G (x3 G) k = (r ≫ thφ G' (x3 G') k) ≫ m.F := fun k => by
    rw [Category.assoc, Category.assoc]
    exact congrArg (r ≫ ·) (m.psum_comm k.down).symm
  refine (val_of (φ := thφ G (x3 G)) (ε := thε) c (r ≫ m.F3) z J (fun k => J ((r ≫ thφ G' (x3 G') k) ≫ m.F))
    (fun k => by rw [e])).trans ?_
  have h1 : r z ∈ LB.wchart (L.pull m.F) (thφ G' (x3 G')) fun k _ => J ((r ≫ thφ G' (x3 G') k) ≫ m.F) :=
    Set.mem_iInter.2 fun k => Set.mem_iInter.2 fun _ => hJ ((r ≫ thφ G' (x3 G') k) ≫ m.F)
  exact ((gm_res r z _ h1 _).trans (gm_pull r m.F3 z _ (m.theta_le L _ h1) _)).symm
end GlobalTheory.PushFirstLaw
