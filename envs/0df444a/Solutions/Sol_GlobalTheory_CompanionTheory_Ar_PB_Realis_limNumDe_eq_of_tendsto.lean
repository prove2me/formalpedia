-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.PB.Realis.limNumDe_eq_of_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:35:46.764668+00:00
-- url     : https://prove2.me/submissions/1f196ae9-d441-45f1-bf06-b06f0e3f5ac5

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
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_PB_AnSys_nComp_pos
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_PB_Realis_nComp_pos
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_PB_Realis_num_eq

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
theorem _root_.solution {w : Fin (D + 1) → σ} {L : ℝ}
    (h : Tendsto (fun t => Re.numDe II t w) (𝓝[>] 0) (𝓝 L)) : Re.limNumDe II w = L := by
  have h1 : Tendsto (fun t => Re.num II t w) (𝓝[>] 0) (𝓝 (S.nComp * L)) := by
    simp only [num_eq]
    exact h.const_mul _
  rw [limNumDe, limNum, h1.limUnder_eq, mul_div_cancel_left₀ _ (Nat.cast_ne_zero.2 Re.nComp_pos.ne')]
end GlobalTheory.CompanionTheory.Ar.PB.Realis
