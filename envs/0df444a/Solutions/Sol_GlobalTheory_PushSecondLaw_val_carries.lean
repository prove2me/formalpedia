-- Prove2me | solution 1 for GlobalTheory.PushSecondLaw.val_carries
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T04:16:12.031563+00:00
-- url     : https://prove2.me/submissions/7fc930ab-3d69-4c3d-a385-059db4707c66

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_AdditionLawSecondIdentity
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ExistsSecondPartialLaw
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_SecondPartialLawPushAlongTripleMap
import Theorems.Thm_GlobalTheory_PushSecondLaw_val_pmaps
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_maps_iff


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
theorem _root_.solution {g : LB.Gen (LB.LinComb L' φ' ε)} {c : LB.Gen (LB.LinComb L (fun k => φ' k ≫ F) ε)}
    (H : Carries L F w φ' ε g c) (hJ : Good L z J) (hJ' : Good L' z J') (r : Z ⟶ Y') :
    val c r z J = (∏ k, (fun q => gw w q z (J (q ≫ F)) (J' q)) (r ≫ φ' k) ^ ε k) * val g r z J' := by
  have P : PMaps w φ' (fun k => φ' k ≫ F) ε g c (𝟙 Y') :=
    (maps_iff w φ' _ ε g c (𝟙 Y') (flatGen L F φ' ε c) (fun j => wchart_pull_le L F φ' j) (fun j => rfl)).1 H
  have e := val_pmaps P (fun k => (Category.id_comp _).symm) hJ hJ' r
  rwa [Category.comp_id] at e
end GlobalTheory.PushSecondLaw
