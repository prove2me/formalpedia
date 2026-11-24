-- Prove2me | solution 1 for GlobalTheory.PowGerm.NabJet.constantCoeff_DmonN_congr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T20:45:41.994618+00:00
-- url     : https://prove2.me/submissions/d850a77b-c1c5-4b43-aed4-1f62e128e86b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Jets_JetsOnCopiesCompatibleFrames
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_TwistBCPf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ConstantCoeffDmonNCongr
import Theorems.Thm_GlobalTheory_PowGerm_NabJet_coeff_foldr_DofN_congr

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.MainNotions.ModuliIntegralCharts.H1.BoxTuple Formalism.MainNotions.ModuliIntegralCharts.H1.BidegreeTwoJet GlobalTheory GlobalTheory.PowGerm
open ReciprocityTheory.ChartRestriction.G.TB (colM dAct)
open GlobalTheory GlobalTheory.PowGerm GlobalTheory.PowGerm.NabJet
open MvPowerSeries
variable {k : Type} [CommRing k] {d n : ℕ}
namespace GlobalTheory.PowGerm.NabJet
theorem _root_.solution (F : Fin d → PS k 2 d) {Ix : Type} [Fintype Ix] (cp : Ix → Fin n) (u : Ix → Fin d → k)
    (m : Ix →₀ ℕ) (f g : PS k n d)
    (h : ∀ mo : Fin n × Fin d →₀ ℕ, mo.degree ≤ m.degree → coeff mo f = coeff mo g) :
    constantCoeff (DmonN F cp u m f) = constantCoeff (DmonN F cp u m g) := by
  rw [← coeff_zero_eq_constantCoeff_apply, ← coeff_zero_eq_constantCoeff_apply]
  unfold DmonN
  refine coeff_foldr_DofN_congr F cp u m f g _ 0 (fun mo' h' => h mo' ?_) 0 (by simp)
  rwa [Finset.sum_map_toList, ← Finsupp.degree_eq_sum, zero_add] at h'
end GlobalTheory.PowGerm.NabJet
