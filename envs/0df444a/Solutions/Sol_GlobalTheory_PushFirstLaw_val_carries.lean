-- Prove2me | solution 1 for GlobalTheory.PushFirstLaw.val_carries
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T03:47:58.190415+00:00
-- url     : https://prove2.me/submissions/74cd7e4a-d2dd-424d-945c-569bf330b9f3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_AdditionLawSecondIdentity
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ExistsSecondPartialLaw
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_FirstPartialLawPushAlongTripleMap
import Theorems.Thm_GlobalTheory_PushFirstLaw_val_maps
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
variable {X X' Y Z : Scheme.{0}} {L' : LB X'} {L : LB X} {F : X' ⟶ X} (w : LB.Iso L' (L.pull F))
  (z : Z) (J : (Z ⟶ X) → L.ι) (J' : (Z ⟶ X') → L'.ι)
variable {w z J J'}
namespace GlobalTheory.PushFirstLaw
theorem _root_.solution (hJ : Good L z J) (hJ' : Good L' z J') {K : Type} [Fintype K] {φ : K → (Y ⟶ X')} {ε : K → ℤ}
    {g : LB.Gen (LB.LinComb L' φ ε)} {g' : LB.Gen (LB.LinComb L (fun k => φ k ≫ F) ε)}
    (h : Carries L F w φ ε g g') (r : Z ⟶ Y) :
    val g' r z J = (∏ k, isoVal w z J J' (r ≫ φ k) ^ ε k) * val g r z J' := by
  refine Eq.trans ?_ (val_maps hJ hJ' h r)
  rw [val_of g' r z J (fun k => J ((r ≫ φ k) ≫ F)) (fun k => by rw [Category.assoc])]
  have h1 : r z ∈ LB.wchart (L.pull F) φ fun k _ => J ((r ≫ φ k) ≫ F) :=
    Set.mem_iInter.2 fun k => Set.mem_iInter.2 fun _ => hJ ((r ≫ φ k) ≫ F)
  exact (gm_res r z _ h1 _).symm
end GlobalTheory.PushFirstLaw
