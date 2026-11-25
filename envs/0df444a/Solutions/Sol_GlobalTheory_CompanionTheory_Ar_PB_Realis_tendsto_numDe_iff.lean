-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.PB.Realis.tendsto_numDe_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:33:33.334694+00:00
-- url     : https://prove2.me/submissions/f8e1b888-6b8d-4286-9bec-93a4fad0fe58

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
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_PB_Realis_numDe_eq
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_PB_Realis_num_eq
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_PB_Realis_limNum_eq

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
open GlobalTheory.CompanionTheory.Ar.PB.Realis
variable {D : ℕ} {σ : Type} {S : AnSys D σ} {P : Ideal (MRing ι)} (Re : Realis S P) (II : IntersectionSystem)
namespace GlobalTheory.CompanionTheory.Ar.PB.Realis
theorem _root_.solution (w : Fin (D + 1) → σ) :
    Tendsto (fun t => Re.numDe II t w) (𝓝[>] 0) (𝓝 (Re.limNumDe II w)) ↔
      Tendsto (fun t => Re.num II t w) (𝓝[>] 0) (𝓝 (Re.limNum II w)) := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · simp only [num_eq, limNum_eq]
    exact h.const_mul _
  · simp only [numDe_eq, limNumDe]
    exact h.div_const _
end GlobalTheory.CompanionTheory.Ar.PB.Realis
