-- Prove2me | solution 1 for GlobalTheory.ChartCmp.Axes.jEq_ev
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T02:38:15.608355+00:00
-- url     : https://prove2.me/submissions/7ee6d218-4f72-4930-bf01-aaa3d6de5fb0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_AdditionLawSecondIdentity
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GaugeTrans
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_FormalChartJetRelUnitOneOnAxes
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_Tri_prod
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gt_hasSubst


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.TB (dLin transF IsInvPair dAct)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ChartCmp
open ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
open GlobalTheory GlobalTheory.ChartCmp GlobalTheory.ChartCmp.Axes
variable {R : Type} [CommRing R]
namespace GlobalTheory.ChartCmp.Axes
theorem _root_.solution {d n n' m : ℕ} (a : Fin n → Pt R n' d) (ha : ∀ j, GP (a j)) {f g : PS R n d} (h : JEq m f g) :
    JEq m (ev a f) (ev a g) := by
  classical
  intro e he
  unfold ev
  rw [MvPowerSeries.coeff_subst (gt_hasSubst a ha), MvPowerSeries.coeff_subst (gt_hasSubst a ha)]
  refine finsum_congr fun c => ?_
  by_cases hc : c.degree ≤ m
  · rw [h c hc]
  · have : MvPowerSeries.coeff e (c.prod fun s k => (a s.1 s.2) ^ k) = 0 := by
      apply MvPowerSeries.coeff_of_lt_order
      refine lt_of_lt_of_le ?_ (MvPowerSeries.le_order_prod _ _)
      have h1 : ((c.degree : ℕ) : ℕ∞) ≤ ∑ s ∈ c.support, MvPowerSeries.order ((a s.1 s.2) ^ c s) := by
        rw [Finsupp.degree_apply, Nat.cast_sum]
        refine Finset.sum_le_sum fun s _ => ?_
        exact MvPowerSeries.le_order_pow_of_constantCoeff_eq_zero _ (ha s.1 s.2)
      refine lt_of_lt_of_le ?_ h1
      exact_mod_cast (by omega : e.degree < c.degree)
    rw [this, smul_zero, smul_zero]
end GlobalTheory.ChartCmp.Axes
