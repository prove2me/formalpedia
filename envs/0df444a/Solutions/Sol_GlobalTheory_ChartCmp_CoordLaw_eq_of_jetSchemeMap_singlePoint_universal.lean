-- Prove2me | solution 1 for GlobalTheory.ChartCmp.CoordLaw.eq_of_jetSchemeMap_singlePoint_universal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T02:41:21.453224+00:00
-- url     : https://prove2.me/submissions/1ddaecc6-b157-41ac-89cb-dc7b7a52a690

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_AdditionLawSecondIdentity
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExpChartJet
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_ChartLawActionEqTransportedOfCoordRel
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpChartJet_aug_comp_jetSubstPS
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpChartJet_jetSubstPS_mk
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_GermD_homAt_comp
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_GermFun_psJet_inj
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_jet_ext
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_ker_jetAug_pow


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
theorem _root_.solution {G : Over (Sp V)} [GrpObj G] {x : ∀ m, jOG (𝟙 (Sp V)) d m 1 ⟶ G}
    (hx : GlobalTheory.PowGerm.IsUnivJ G (Fin 1 × Fin d) x) {n : ℕ} {a b : Pt V n d}
    (ha : ∀ i, MvPowerSeries.constantCoeff (a i) = 0) (hb : ∀ i, MvPowerSeries.constantCoeff (b i) = 0)
    (h : ∀ m, sub1 m a ≫ x m = sub1 m b ≫ x m) : a = b := by
  funext i
  refine GermFun.psJet_inj fun m => ?_
  have hk : RingHom.ker (jetAug : Jet V (Fin n × Fin d) m →ₐ[V] V) ^ (m + 1) = ⊥ := by
    have ea : (jetAug : Jet V (Fin n × Fin d) m →ₐ[V] V) = Chart.jetAug V _ m := Chart.jet_ext fun j => rfl
    rw [ea]
    exact Chart.ker_jetAug_pow _ m
  have aa := ExpChartJet.aug_comp_jetSubstPS m (fun p : Fin 1 × Fin d => a p.2) (fun p => ha p.2)
  have ab := ExpChartJet.aug_comp_jetSubstPS m (fun p : Fin 1 × Fin d => b p.2) (fun p => hb p.2)
  have h1 : Formalism.L2.Pj.homAt (𝟙 (Sp V)) (jetAug : Jet V (Fin n × Fin d) m →ₐ[V] V) ≫ (sub1 m a ≫ x m) = 1 := by
    rw [sub1, ← Category.assoc, GermD.homAt_comp, aa]
    exact hx.2.1 m
  have e := (hx.2.2 _ jetAug m hk _ h1).unique ⟨aa, rfl⟩ ⟨ab, h m⟩
  have e' := AlgHom.congr_fun e (Ideal.Quotient.mk _ (MvPolynomial.X ((0 : Fin 1), i)))
  rwa [ExpChartJet.jetSubstPS_mk m (fun p : Fin 1 × Fin d => a p.2) (fun p => ha p.2),
    ExpChartJet.jetSubstPS_mk m (fun p : Fin 1 × Fin d => b p.2) (fun p => hb p.2)] at e'
end GlobalTheory.ChartCmp.CoordLaw
