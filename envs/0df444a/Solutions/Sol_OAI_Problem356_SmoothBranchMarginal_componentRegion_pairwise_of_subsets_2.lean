-- Prove2me | solution 2 for OAI.Problem356.SmoothBranchMarginal.componentRegion_pairwise_of_subsets
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T23:11:41.189994+00:00
-- url     : https://prove2.me/submissions/59b50002-58cc-4b46-8657-a40a360b2679

-- Generated from openai/math@1581d4c lean/OAI/Analysis/CoulombTransport/ComponentRegions.lean:L9-L29
-- (upload_full_project.md Phase 4): solution for node OAI.Problem356.SmoothBranchMarginal.componentRegion_pairwise_of_subsets. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_CoulombCounterexample
import Definitions.Def_OAI_Analysis_CoulombTransport_AxisHessian
import Definitions.Def_OAI_Analysis_CoulombTransport_BranchCoupling
import Definitions.Def_OAI_Analysis_CoulombTransport_CoulombEstimates
import Definitions.Def_OAI_Analysis_CoulombTransport_BranchSeparation
import Definitions.Def_OAI_Analysis_CoulombTransport_GraphBridge
import Definitions.Def_OAI_Analysis_CoulombTransport_DualCertificate
import Definitions.Def_OAI_Analysis_CoulombTransport_OptimalLocalization
import Definitions.Def_OAI_Analysis_CoulombTransport_Calibration
import Definitions.Def_OAI_Analysis_CoulombTransport_CertificateAttainment
import Definitions.Def_OAI_Analysis_CoulombTransport_SplitMeasure
import Definitions.Def_OAI_Analysis_CoulombTransport_PartitionLabel
import Definitions.Def_OAI_Analysis_CoulombTransport_CenterCertificate
import Definitions.Def_OAI_Analysis_CoulombTransport_CommonBranches
import Definitions.Def_OAI_Analysis_CoulombTransport_DensityMeasure
import Definitions.Def_OAI_Analysis_CoulombTransport_ComponentPotential
import Definitions.Def_OAI_Analysis_CoulombTransport_LocalImplicit
import Definitions.Def_OAI_Analysis_CoulombTransport_HessianCLM
import Definitions.Def_OAI_Analysis_CoulombTransport_CoulombCalculus
import Definitions.Def_OAI_Analysis_CoulombTransport_StationaryEquation
import Definitions.Def_OAI_Analysis_CoulombTransport_HessianMatrix
import Definitions.Def_OAI_Analysis_CoulombTransport_CoulombCoercivity
import Definitions.Def_OAI_Analysis_CoulombTransport_LocalCertificate
import Definitions.Def_OAI_Analysis_CoulombTransport_StationaryMap
import Definitions.Def_OAI_Analysis_CoulombTransport_LocalBranchMeasure
import Definitions.Def_OAI_Analysis_CoulombTransport_SmoothPushforward
import Definitions.Def_OAI_Analysis_CoulombTransport_GluedCertificate
import Definitions.Def_OAI_Analysis_CoulombTransport_GoodTypePermutation
import Definitions.Def_OAI_Analysis_CoulombTransport_IsometryTransport
import Definitions.Def_OAI_Analysis_CoulombTransport_SmoothBranchMarginal
import Definitions.Def_OAI_Analysis_CoulombTransport_StateDual
import Definitions.Def_OAI_Analysis_CoulombTransport_CoulombSupportExistence
import Definitions.Def_OAI_Analysis_CoulombTransport_FiveComponentGeometry
import Definitions.Def_OAI_Analysis_CoulombTransport_CenterAxis

-- ---- from OAI.Analysis.CoulombTransport.ComponentRegions ----
namespace OAI

noncomputable section

namespace Problem356.SmoothBranchMarginal

/-- Component containment in the disjoint five certificate regions supplies
exactly the disjointness input of the smooth marginal construction. -/
theorem componentRegion_pairwise_of_subsets
    {B : Set E3} {e : Fin 4 → OpenPartialHomeomorph E3 E3}
    {U : Fin 5 → Set E3}
    (hU : Pairwise (fun i j => Disjoint (U i) (U j)))
    (hB : B ⊆ U 0) (he : ∀ i, e i '' B ⊆ U i.succ) :
    Pairwise (fun i j => Disjoint (componentRegion B e i) (componentRegion B e j)) := by
  intro i j hij
  cases i with
  | none =>
    cases j with
    | none => exact (hij rfl).elim
    | some j =>
      exact (hU (Fin.succ_ne_zero j).symm).mono hB (he j)
  | some i =>
    cases j with
    | none =>
      exact (hU (Fin.succ_ne_zero i)).mono (he i) hB
    | some j =>
      exact (hU (fun h => hij (congrArg some (Fin.succ_injective 4 h)))).mono (he i) (he j)

end Problem356.SmoothBranchMarginal

end

end OAI

-- ---- platform node ----
open OAI OAI.Problem356 OAI.Problem356.SmoothBranchMarginal


theorem solution : type_of% @_root_.OAI.Problem356.SmoothBranchMarginal.componentRegion_pairwise_of_subsets := @_root_.OAI.Problem356.SmoothBranchMarginal.componentRegion_pairwise_of_subsets
