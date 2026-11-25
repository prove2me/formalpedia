-- Prove2me | solution 1 for GlobalTheory.ChartCmp.CoordDir.tp_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T02:38:22.316164+00:00
-- url     : https://prove2.me/submissions/e8da730e-2867-4bc7-ba92-9f36000e7312

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_AdditionLawSecondIdentity
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExpChartJet
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_TangentDirectionTwoChartsLinearPart
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpChartJetA_tp_mk
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_GermD_jet_hom_ext
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp


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
namespace GlobalTheory.ChartCmp.CoordDir
theorem _root_.solution : (tp (0 : Fin 1 × Fin d → V)) =
      (Algebra.ofId V (DualNumber V)).comp (jetAug : Jet V (Fin 1 × Fin d) (0 + 1) →ₐ[V] V) := by
  apply jet_hom_ext
  intro q
  rw [tp_mk, AlgHom.comp_apply]
  show TrivSqZeroExt.inr (0 : V) =
    algebraMap V (DualNumber V) (MvPolynomial.aeval (fun _ => (0 : V)) (MvPolynomial.X q))
  rw [MvPolynomial.aeval_X, map_zero, TrivSqZeroExt.inr_zero]
end GlobalTheory.ChartCmp.CoordDir
