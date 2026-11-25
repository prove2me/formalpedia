-- Prove2me | solution 1 for GlobalTheory.ChartCmp.Coord.subst_eq_X
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T02:59:47.566174+00:00
-- url     : https://prove2.me/submissions/6afdbd7f-c097-4e1d-9ceb-f9e8c1f717b3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_AdditionLawSecondIdentity
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExpChartJet
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GaugeUniqB
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExpUniqLoc
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermFunPf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_ExistsCoordinateRelationUniversalJets
import Theorems.Thm_GlobalTheory_ChartCmp_Coord_uniq
import Theorems.Thm_GlobalTheory_ChartCmp_Coord_aug_comp_subst
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpChartJet_jetSubstPS_mk
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpChartJet_jetSubstPS_psJet
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpUniqLoc_ker_aug_pow
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpUniqLoc_uniq
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_GaugeR_psJet_eq_mk
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_GermD_homAt_comp
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_GermD_homAt_id
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_GermFun_psJet_inj
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
open GlobalTheory GlobalTheory.ChartCmp GlobalTheory.ChartCmp.Coord
open Formalism.MainNotions.ModuliIntegralCharts.H1
variable {V : Type} [CommRing V]
namespace GlobalTheory.ChartCmp.Coord
theorem _root_.solution {G : Over (Sp V)} [GrpObj G] {κ κ' : Type} [Fintype κ] [DecidableEq κ] [Fintype κ'] [DecidableEq κ']
    {x : GlobalTheory.PowGerm.JetPts G κ} (hx : GlobalTheory.PowGerm.IsUnivJ G κ x) {x' : GlobalTheory.PowGerm.JetPts G κ'}
    {φ : κ → MvPowerSeries κ' V} (h0 : ∀ i, MvPowerSeries.constantCoeff (φ i) = 0)
    (hφ : ∀ m, x' m = Formalism.L2.Pj.homAt (𝟙 (Sp V)) (jetSubstPS (m := m) φ) ≫ x m)
    {φi : κ' → MvPowerSeries κ V} (h0i : ∀ i, MvPowerSeries.constantCoeff (φi i) = 0)
    (hφi : ∀ m, x m = Formalism.L2.Pj.homAt (𝟙 (Sp V)) (jetSubstPS (m := m) φi) ≫ x' m) (i : κ) :
    MvPowerSeries.subst φi (φ i) = MvPowerSeries.X i := by
  apply GermFun.psJet_inj
  intro m
  have e : (jetSubstPS (m := m) φi).comp (jetSubstPS (m := m) φ) = AlgHom.id V _ := by
    refine uniq hx (jetAug : Jet V κ m →ₐ[V] V) m (ExpUniqLoc.ker_aug_pow le_rfl) ?_ ?_ ?_
    · rw [← AlgHom.comp_assoc, aug_comp_subst m φi h0i, aug_comp_subst m φ h0]
    · rfl
    · rw [← GermD.homAt_comp, Category.assoc, ← hφ, ← hφi, GermD.homAt_id, Category.id_comp]
  have e' := DFunLike.congr_fun e (Ideal.Quotient.mk _ (MvPolynomial.X i))
  rw [AlgHom.comp_apply, ExpChartJet.jetSubstPS_mk m φ h0, ExpChartJet.jetSubstPS_psJet m φi h0i] at e'
  rw [e', ← MvPolynomial.coe_X]
  exact (GaugeR.psJet_eq_mk m _ _ fun e _ => (MvPolynomial.coeff_coe _ _).symm).symm
end GlobalTheory.ChartCmp.Coord
