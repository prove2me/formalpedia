-- Prove2me | solution 1 for GlobalTheory.ChartCmp.CarryCalc.val_of_carries
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T14:32:15.442604+00:00
-- url     : https://prove2.me/submissions/5cad6385-f643-49a6-9814-34d7bf60bfc6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_AdditionLawSecondIdentity
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsMonHomOfMul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBTransport
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBPull
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_CarriesLinCombGeneratorCalculus
import Theorems.Thm_GlobalTheory_ChartCmp_CarryCalc_carries_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans


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
open GlobalTheory GlobalTheory.ChartCmp GlobalTheory.ChartCmp.CarryCalc
variable {X X' Y : Scheme.{0}} {L' : LB X'} {L : LB X} {F : X' ⟶ X} {K : Type} [Fintype K]
namespace GlobalTheory.ChartCmp.CarryCalc
theorem _root_.solution {w : LB.Iso L' (L.pull F)} {φ : K → (Y ⟶ X')} {ε : K → ℤ} {g : LB.Gen (LB.LinComb L' φ ε)}
    {g' : LB.Gen (LB.LinComb L (fun k => φ k ≫ F) ε)} (H : Carries L F w φ ε g g') {Z : Scheme.{0}} (r : Z ⟶ Y) {z : Z}
    {J : (Z ⟶ X) → L.ι} {J' : (Z ⟶ X') → L'.ι} (hJ : Good L z J) (hJ' : Good L' z J') :
    val g' r z J = (∏ k, fac w z J J' (r ≫ φ k) ^ ε k) * val g r z J' := by
  refine ((carries_iff w φ ε g g').1 H Z r z _ _ (hJ.mem _ r) (hJ'.mem _ r)).trans (congrArg₂ (· * ·) ?_ rfl)
  simp only [pw, fac, Category.assoc]
end GlobalTheory.ChartCmp.CarryCalc
