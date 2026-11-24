-- Prove2me | solution 1 for GlobalTheory.LinkLaw.exists_subst
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T19:00:48.691817+00:00
-- url     : https://prove2.me/submissions/514ecea4-d8a6-4d41-bfe7-5f31fdb6e80d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Jets_JetsOnCopiesCompatibleFrames
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_TwistBCPf
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_FBIdJet
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_ExistsToJetEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_IsLawOfOfMatch
import Theorems.Thm_GlobalTheory_JetSer_jetAlg


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
theorem _root_.solution {σ κ : Type} [Finite σ] [Finite κ] (c : σ → MvPowerSeries κ V)
    (hc : ∀ j, MvPowerSeries.constantCoeff (c j) = 0) (m : ℕ) :
    ∃ Φ : Jet V σ m →ₐ[V] Chart.JetR V κ m,
      (∀ j, Φ (Ideal.Quotient.mk _ (MvPolynomial.X j)) = JetSer.toJet m (c j)) ∧
      ∀ g : MvPowerSeries σ V, Φ (JetSer.toJet m g) = JetSer.toJet m (MvPowerSeries.subst c g) := by
  obtain ⟨⟨Φ, hΦ⟩, hsub⟩ := (JetSer.jetAlg V κ).2.2.2.2 σ c hc m
  exact ⟨Φ, hΦ, hsub Φ hΦ⟩
end GlobalTheory.LinkLaw
