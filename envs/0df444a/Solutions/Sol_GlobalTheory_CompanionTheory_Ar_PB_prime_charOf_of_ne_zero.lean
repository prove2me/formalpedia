-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.PB.prime_charOf_of_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T12:18:44.189799+00:00
-- url     : https://prove2.me/submissions/adbc3a65-68a0-4fe6-86bb-aa03f0fbc15a

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterRes
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterNamed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_KleimanNefness_TargetSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_KleimanNefness_KleimanSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_ExistsUniqueStatement
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_GenericComplexPoint
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_DivisibilityTowers_Birational
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_MetricPeriods_IsTwiceDifferentiableAt
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_MetricPeriods_MetricsProjectionFormulaNef

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial Filter Topology
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
namespace GlobalTheory.CompanionTheory.Ar.PB
theorem _root_.solution {W : Ideal (MRing ι)} (hW : W.IsPrime) (h : charOf W ≠ 0) : (charOf W).Prime := by
  have hI : (W.comap (C : ℤ →+* MRing ι)).IsPrime := Ideal.comap_isPrime _ _
  have h0 : Submodule.IsPrincipal.generator (W.comap (C : ℤ →+* MRing ι)) ≠ 0 := fun e => h (by simp [charOf, e])
  rw [← Ideal.span_singleton_generator (W.comap (C : ℤ →+* MRing ι)), Ideal.span_singleton_prime h0] at hI
  exact Int.prime_iff_natAbs_prime.1 hI
end GlobalTheory.CompanionTheory.Ar.PB
