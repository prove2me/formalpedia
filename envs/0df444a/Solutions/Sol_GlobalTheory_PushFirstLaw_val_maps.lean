-- Prove2me | solution 1 for GlobalTheory.PushFirstLaw.val_maps
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T02:29:04.392125+00:00
-- url     : https://prove2.me/submissions/828b1c6a-2ab2-469c-9719-de073be98a72

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_AdditionLawSecondIdentity
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ExistsSecondPartialLaw
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_FirstPartialLawPushAlongTripleMap
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_pull
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_res


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
    {g : LB.Gen (LB.LinComb L' φ ε)} {b : LB.Gen (LB.LinComb (L.pull F) φ ε)}
    (h : LB.Gen.Maps (LB.linCombIso w φ ε) g b) (r : Z ⟶ Y) :
    gm r z (LB.wchart (L.pull F) φ fun k _ => J ((r ≫ φ k) ≫ F)) (b.s fun k _ => J ((r ≫ φ k) ≫ F)) =
      (∏ k, isoVal w z J J' (r ≫ φ k) ^ ε k) * val g r z J' := by
  have h1 : r z ∈ LB.wchart (L.pull F) φ fun k _ => J ((r ≫ φ k) ≫ F) :=
    Set.mem_iInter.2 fun k => Set.mem_iInter.2 fun _ => hJ ((r ≫ φ k) ≫ F)
  have hm : r z ∈ LB.wchart (L.pull F) φ (fun k _ => J ((r ≫ φ k) ≫ F)) ⊓ LB.wchart L' φ (fun k => J' (r ≫ φ k)) :=
    ⟨h1, hJ'.mem φ r⟩
  refine (gm_res r z _ hm _).symm.trans ((congrArg (gm r z _)
    (h (fun k _ => J ((r ≫ φ k) ≫ F), fun k => J' (r ≫ φ k)))).trans ((map_mul _ _ _).trans
      (congrArg₂ (· * ·) ?_ (gm_res r z _ hm _))))
  refine (map_prod _ _ _).trans (Finset.prod_congr rfl fun a _ => (map_zpow _ _ _).trans (congrArg (· ^ ε a) ?_))
  have ha : (φ a) (r z) ∈ (L.pull F).U (fun _ => J ((r ≫ φ a) ≫ F)) ⊓ L'.U (J' (r ≫ φ a)) :=
    ⟨LB.wchart_le (L.pull F) φ _ a hm.1, LB.wchart_le L' φ _ a hm.2⟩
  exact (gm_res r z _ hm _).trans (gm_pull r (φ a) z _ ha _)
end GlobalTheory.PushFirstLaw
