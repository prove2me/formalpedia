-- Prove2me | solution 1 for GlobalTheory.LinkLaw.jetSubstP_coord
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:55:06.616664+00:00
-- url     : https://prove2.me/submissions/1fe59fa2-70e3-4163-994d-48408aff06f6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Jets_JetsOnCopiesCompatibleFrames
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_TwistBCPf
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_FBIdJet
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_ExistsToJetEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_IsLawOfOfMatch
import Theorems.Thm_GlobalTheory_LinkLaw_jetMap_coord
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_FBIdJet_psTrunc_eq


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.MainNotions.ModuliIntegralCharts.H1.BoxTuple Formalism.MainNotions.ModuliIntegralCharts.H1.BidegreeTwoJet GlobalTheory GlobalTheory.PowGerm
open ReciprocityTheory.ChartRestriction.G.TB (colM dAct)
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.LinkLaw
variable {V : Type} [CommRing V]
namespace GlobalTheory.LinkLaw
theorem _root_.solution {κ κ' : Type} [Fintype κ'] [DecidableEq κ'] (m : ℕ) (F : κ → MvPowerSeries κ' V) (j : κ)
    (h : MvPowerSeries.constantCoeff (F j) = 0) :
    jetSubstP m (fun p => psTrunc m (F p)) (Ideal.Quotient.mk _ (MvPolynomial.X j)) = JetSer.toJet m (F j) := by
  unfold jetSubstP
  rw [jetMap_coord]
  have h0 : MvPolynomial.constantCoeff (psTrunc m (F j)) = 0 := by
    rw [Formalism.MainNotions.ModuliIntegralCharts.H1.FBIdJet.psTrunc_eq, MvPolynomial.constantCoeff_eq,
      MvPowerSeries.coeff_truncTotal _ (by simp), MvPowerSeries.coeff_zero_eq_constantCoeff_apply, h]
  rw [h0, map_zero, sub_zero]
  exact congrArg (Ideal.Quotient.mk _) (Formalism.MainNotions.ModuliIntegralCharts.H1.FBIdJet.psTrunc_eq m (F j))
end GlobalTheory.LinkLaw
