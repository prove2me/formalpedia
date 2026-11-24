-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.PB.AnSys.finite_components
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T12:18:37.553194+00:00
-- url     : https://prove2.me/submissions/e48cd87d-3c1a-45dd-962e-e3dba8910522

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
open GlobalTheory.CompanionTheory.Ar.PB.AnSys
variable {e : ℕ} {σ : Type} (S : AnSys e σ)
namespace GlobalTheory.CompanionTheory.Ar.PB.AnSys
theorem _root_.solution : Finite (ConnectedComponents S.X) := by
  let _ : ChartedSpace (Fin e → ℂ) S.X :=
    { atlas := Set.range S.A.chart
      chartAt := fun x => S.A.chart (S.A.cover x).choose
      mem_chart_source := fun x => (S.A.cover x).choose_spec
      chart_mem_atlas := fun _ => ⟨_, rfl⟩ }
  have := ChartedSpace.locallyConnectedSpace (Fin e → ℂ) S.X
  infer_instance
end GlobalTheory.CompanionTheory.Ar.PB.AnSys
