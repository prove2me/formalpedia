-- Prove2me | solution 1 for GlobalTheory.PushSecondLaw.val_pmaps
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T02:22:19.646558+00:00
-- url     : https://prove2.me/submissions/11582460-95b4-4558-82eb-ac4ce6ae3dc5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_AdditionLawSecondIdentity
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ExistsSecondPartialLaw
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_SecondPartialLawPushAlongTripleMap
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
open GlobalTheory GlobalTheory.PushSecondLaw
open MvPolynomial (X)
open GlobalTheory.SecondPartialLaw
variable {X X' Y Y' Z : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X} {w : LB.Iso L' (L.pull F)}
  {K : Type} [Fintype K] {φ' : K → (Y' ⟶ X')} {ε : K → ℤ} {z : Z} {J : (Z ⟶ X) → L.ι} {J' : (Z ⟶ X') → L'.ι}
namespace GlobalTheory.PushSecondLaw
theorem _root_.solution {φ : K → (Y ⟶ X)} {a : LB.Gen (LB.LinComb L' φ' ε)} {t : LB.Gen (LB.LinComb L φ ε)} {h : Y' ⟶ Y}
    (H : PMaps w φ' φ ε a t h) (hc : ∀ k, φ' k ≫ F = h ≫ φ k) (hJ : Good L z J) (hJ' : Good L' z J') (r : Z ⟶ Y') :
    val t (r ≫ h) z J = (∏ k, (fun q => gw w q z (J (q ≫ F)) (J' q)) (r ≫ φ' k) ^ ε k) * val a r z J' := by
  have e := H _ r z (fun k => J ((r ≫ φ' k) ≫ F)) (fun k => J' (r ≫ φ' k)) (fun k => hJ _) (fun k => hJ' _)
  refine Eq.trans ?_ e
  refine val_of _ _ _ _ _ fun k => congrArg J ?_
  rw [Category.assoc, Category.assoc, hc]
end GlobalTheory.PushSecondLaw
