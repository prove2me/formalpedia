-- Prove2me | solution 1 for GlobalTheory.ChartCmp.CoordLaw.jptG_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T03:37:52.176786+00:00
-- url     : https://prove2.me/submissions/201d4c59-353b-4928-9412-d99879d41e3d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_AdditionLawSecondIdentity
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExpChartJet
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_ChartLawActionEqTransportedOfCoordRel
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpChartJet_jetSubstPS_mk
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_FBIdJet_mk_trunc_coe
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_FBIdJet_psTrunc_eq
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_GermD_jetMap_mk
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_GermD_jet_hom_ext


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
open GlobalTheory GlobalTheory.ChartCmp GlobalTheory.ChartCmp.CoordLaw
open Formalism.MainNotions.ModuliIntegralCharts.H1
variable {V : Type} [CommRing V] {d : ℕ}
namespace GlobalTheory.ChartCmp.CoordLaw
theorem _root_.solution {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (t : SAB H (Sp V))
    (x : ∀ m, jOG (𝟙 (Sp V)) d m 1 ⟶ t.G) (m : ℕ) {n : ℕ} (i : Fin n) :
    jptG t (𝟙 (Sp V)) d x m i = sub1 m (pt V d i) ≫ x m := by
  have e : jetCopy (S := V) d m i = jetSubstPS (m := m) (fun p : Fin 1 × Fin d => pt V d i p.2) := by
    apply GermD.jet_hom_ext
    intro p
    rw [ExpChartJet.jetSubstPS_mk m (fun p : Fin 1 × Fin d => pt V d i p.2) (fun _ => MvPowerSeries.constantCoeff_X _),
      jetCopy, GermD.jetMap_mk, MvPolynomial.aeval_X, pt, ← MvPolynomial.coe_X]
    rw [psJet, FBIdJet.psTrunc_eq, FBIdJet.mk_trunc_coe]
  rw [jptG, e]
  rfl
end GlobalTheory.ChartCmp.CoordLaw
