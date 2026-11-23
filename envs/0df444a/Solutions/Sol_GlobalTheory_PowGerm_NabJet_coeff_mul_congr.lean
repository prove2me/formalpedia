-- Prove2me | solution 1 for GlobalTheory.PowGerm.NabJet.coeff_mul_congr
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:15:29.976099+00:00
-- url     : https://prove2.me/submissions/0a97ff0c-6231-40f3-b840-8b3123d51492

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Jets_JetsOnCopiesCompatibleFrames
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_TwistBCPf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ConstantCoeffDmonNCongr

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
theorem _root_.solution (N : ℕ) (f g E : PS k n d)
    (h : ∀ a : Fin n × Fin d →₀ ℕ, a.degree ≤ N → coeff a f = coeff a g)
    (a : Fin n × Fin d →₀ ℕ) (ha : a.degree ≤ N) : coeff a (f * E) = coeff a (g * E) := by
  classical
  rw [coeff_mul, coeff_mul]
  refine Finset.sum_congr rfl fun p hp => ?_
  have hp' : p.1 + p.2 = a := Finset.HasAntidiagonal.mem_antidiagonal.1 hp
  have hd : p.1.degree + p.2.degree = a.degree := by rw [← hp', map_add]
  rw [h p.1 (by omega)]
end GlobalTheory.PowGerm.NabJet
