-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.PB.Realis.PBDe_of_connected
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:34:31.964451+00:00
-- url     : https://prove2.me/submissions/04f7078f-c8e1-4800-b3f6-762c7e354545

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
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_PB_AnSys_nComp_eq_one
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_PB_Realis_FT_eq
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_PB_Realis_PB_eq

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
theorem _root_.solution [Fintype σ] [ConnectedSpace S.X] :
    Re.de = Re.deg ∧ Re.PBDe II = Re.PB II ∧ ∀ t, Re.FTDe II t = Re.FT II t := by
  simp [de, PB_eq, FT_eq, S.nComp_eq_one]
end GlobalTheory.CompanionTheory.Ar.PB.Realis
