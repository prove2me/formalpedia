-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.PB.nefOnFibres_iff_nefAt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:33:39.684813+00:00
-- url     : https://prove2.me/submissions/23a24c0e-5790-469e-85b1-8d1200031195

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
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_PB_prime_charOf_of_ne_zero

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
theorem _root_.solution (P : Ideal (MRing ι)) (a : K → ℤ) :
    NefOnFibres P a ↔ ∀ p : ℕ, p.Prime → NefAt P p a :=
  ⟨fun h p hp W h1 h2 h3 h4 => h W h1 h2 (h3 ▸ hp.ne_zero) h4,
    fun h W h1 h2 h3 h4 => h _ (prime_charOf_of_ne_zero h1.1 h3) W h1 h2 rfl h4⟩
end GlobalTheory.CompanionTheory.Ar.PB
