-- Prove2me | solution 1 for GlobalTheory.ChartCmp.CoordDir.tanPt_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T05:51:51.754945+00:00
-- url     : https://prove2.me/submissions/5b9b57e2-6d06-4439-b171-88e2917f3c07

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_AdditionLawSecondIdentity
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExpChartJet
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_TangentDirectionTwoChartsLinearPart
import Theorems.Thm_GlobalTheory_ChartCmp_CoordDir_tanPt_zero
import Theorems.Thm_GlobalTheory_ChartCmp_CoordDir_tanPt_add
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_Tri_prod


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
open Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.FBIdJet Formalism.MainNotions.ModuliIntegralCharts.H1.GermFun Formalism.MainNotions.ModuliIntegralCharts.H1.GermD
open Formalism.MainNotions.ModuliIntegralCharts.H1.ExpChartJetA Formalism.MainNotions.ModuliIntegralCharts.H1.ExpChartJet
open GlobalTheory GlobalTheory.ChartCmp GlobalTheory.ChartCmp.CoordDir
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {V : Type} [CommRing V]
  {t : SAB H (Sp V)} {d : ℕ}
variable {κ : Type} [Fintype κ] {G : FGLaw V d} {act : 𝓞 E → Fin d → MvPowerSeries (Fin 1 × Fin d) V}
  {tg : κ → (Sp (DualNumber V) ⟶ t.G.left)} {uv : κ → Fin d → V} {x : ∀ m, jOG (𝟙 (Sp V)) d m 1 ⟶ t.G}
namespace GlobalTheory.ChartCmp.CoordDir
theorem _root_.solution (hx : IsChartG t (𝟙 (Sp V)) d G.F act tg uv x) : ∀ (n : ℕ) (f : Fin n → Fin 1 × Fin d → V),
    tanPt x (∑ i, f i) = (List.ofFn fun i => tanPt x (f i)).prod
  | 0, f => by rw [Fin.sum_univ_zero, List.ofFn_zero, List.prod_nil, tanPt_zero hx]
  | n + 1, f => by rw [Fin.sum_univ_succ, tanPt_add hx, solution hx n, List.ofFn_succ, List.prod_cons]
end GlobalTheory.ChartCmp.CoordDir
