-- Prove2me | solution 1 for GlobalTheory.ChartCmp.Coord.exists_coord
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T04:14:03.082085+00:00
-- url     : https://prove2.me/submissions/d28fe8b5-9f51-47ac-8002-6957978827c5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_AdditionLawSecondIdentity
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExpChartJet
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GaugeUniqB
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExpUniqLoc
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermFunPf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_ExistsCoordinateRelationUniversalJets
import Theorems.Thm_GlobalTheory_ChartCmp_Coord_uniq
import Theorems.Thm_GlobalTheory_ChartCmp_Coord_aug_X
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpChartJet_jetSubstPS_mk
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpUniqLoc_aug_comp_trunc
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpUniqLoc_ker_aug_pow
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpUniqLoc_uniq
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_GaugeR_exists_ps_of_compat
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_GaugeR_jetAug_psJet
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_GermD_homAt_comp
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
open GlobalTheory GlobalTheory.ChartCmp GlobalTheory.ChartCmp.Coord
open Formalism.MainNotions.ModuliIntegralCharts.H1
variable {V : Type} [CommRing V]
namespace GlobalTheory.ChartCmp.Coord
theorem _root_.solution {G : Over (Sp V)} [GrpObj G] {κ κ' : Type} [Fintype κ] [DecidableEq κ] [Fintype κ'] [DecidableEq κ']
    {x : GlobalTheory.PowGerm.JetPts G κ} (hx : GlobalTheory.PowGerm.IsUnivJ G κ x) {x' : GlobalTheory.PowGerm.JetPts G κ'}
    (hx' : GlobalTheory.PowGerm.IsUnivJ G κ' x') :
    ∃ φ : κ → MvPowerSeries κ' V, (∀ i, MvPowerSeries.constantCoeff (φ i) = 0) ∧
      ∀ m, x' m = Formalism.L2.Pj.homAt (𝟙 (Sp V)) (jetSubstPS (m := m) φ) ≫ x m := by
  have h := fun m => (hx.2.2 (Jet V κ' m) jetAug m (ExpUniqLoc.ker_aug_pow le_rfl) (x' m) (hx'.2.1 m)).exists
  choose ψ hψa hψ using h
  have hc : ∀ m, (jetTrunc : Jet V κ' (m + 1) →ₐ[V] Jet V κ' m).comp (ψ (m + 1)) =
      (ψ m).comp (jetTrunc : Jet V κ (m + 1) →ₐ[V] Jet V κ m) := by
    intro m
    refine uniq hx (jetAug : Jet V κ' m →ₐ[V] V) (m + 1) (ExpUniqLoc.ker_aug_pow (by omega)) ?_ ?_ ?_
    · rw [← AlgHom.comp_assoc, ExpUniqLoc.aug_comp_trunc, hψa]
    · rw [← AlgHom.comp_assoc, hψa, ExpUniqLoc.aug_comp_trunc]
    · rw [← GermD.homAt_comp, ← GermD.homAt_comp, Category.assoc, Category.assoc, hx.1, ← hψ, ← hψ, hx'.1]
  have hs := fun i : κ => GaugeR.exists_ps_of_compat
    (fun m => ψ m (Ideal.Quotient.mk _ (MvPolynomial.X i))) (fun m => DFunLike.congr_fun (hc m) _)
  choose φ hφ using hs
  have h0 : ∀ i, MvPowerSeries.constantCoeff (φ i) = 0 := by
    intro i
    rw [← GaugeR.jetAug_psJet 0, hφ, ← AlgHom.comp_apply, hψa, aug_X]
  refine ⟨φ, h0, fun m => ?_⟩
  have : jetSubstPS (m := m) φ = ψ m := by
    apply GermD.jet_hom_ext
    intro i
    rw [ExpChartJet.jetSubstPS_mk m φ h0, hφ]
  rw [this]
  exact hψ m
end GlobalTheory.ChartCmp.Coord
