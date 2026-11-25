-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.isUnit_algebraMap_locRing
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T16:14:11.083799+00:00
-- url     : https://prove2.me/submissions/6cda1ae4-96c7-42cf-a4cf-10a6cb1824f3

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_IsSncModel
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_BlowupProjections_BlowupProjStatement
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_DivisibilityTowers_Proportional
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterAlgRes
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterPCProof
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_LocTransfer
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_Immersion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterMinor
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_FiniteMinimalPrimes
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_SncResolutionCompactEmbeddedStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_SncResolutionTransitionPolynomialStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_SncResolutionCoverAndConeStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_SncResolutionLocalChartPolynomialStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_SncResolutionRegularLocalRingStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_SncResolutionBoundaryNormalCrossingStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_SncModelEmbeddedLogResolution

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.Cmp.SncRes
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.AnForm.M
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
namespace GlobalTheory.CompanionTheory.Ar.Cmp.SncRes
theorem _root_.solution {n : ℕ} (I : Ideal (MvPolynomial (Fin n) ℂ)) (pt : Fin n → ℂ)
    (g : MvPolynomial (Fin n) ℂ) (hg : eval pt g ≠ 0) :
    IsUnit (algebraMap _ (ReciprocityTheory.AnForm.R.locRing I pt) g) := by
  have := (IsLocalization.map_units (ReciprocityTheory.AnForm.R.locPt pt)
    (⟨g, fun h => hg (RingHom.mem_ker.mp h)⟩ : (ReciprocityTheory.AnForm.R.ptIdeal pt).primeCompl)).map
    (algebraMap (ReciprocityTheory.AnForm.R.locPt pt) (ReciprocityTheory.AnForm.R.locRing I pt))
  rwa [← IsScalarTower.algebraMap_apply] at this
end GlobalTheory.CompanionTheory.Ar.Cmp.SncRes
