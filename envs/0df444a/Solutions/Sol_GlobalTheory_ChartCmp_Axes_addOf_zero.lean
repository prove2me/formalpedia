-- Prove2me | solution 1 for GlobalTheory.ChartCmp.Axes.addOf_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T02:48:38.705942+00:00
-- url     : https://prove2.me/submissions/b323fe9b-fe55-4f17-acf9-155d4f3016a3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_AdditionLawSecondIdentity
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GaugeTrans
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_FormalChartJetRelUnitOneOnAxes

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
theorem _root_.solution {d n : ℕ} (F : Fin d → PS R 2 d) (hF : ∀ i, MvPowerSeries.constantCoeff (F i) = 0) :
    addOf F (0 : Pt R n d) 0 = 0 := by
  funext i
  change MvPowerSeries.subst (fun p : Fin 2 × Fin d => (![(0 : Pt R n d), 0] p.1) p.2) (F i) = 0
  have e : (fun p : Fin 2 × Fin d => (![(0 : Pt R n d), 0] p.1) p.2) = 0 := by
    funext p
    obtain ⟨j, l⟩ := p
    fin_cases j <;> rfl
  rw [e]
  exact MvPowerSeries.subst_zero_of_constantCoeff_zero (hF i)
end GlobalTheory.ChartCmp.Axes
