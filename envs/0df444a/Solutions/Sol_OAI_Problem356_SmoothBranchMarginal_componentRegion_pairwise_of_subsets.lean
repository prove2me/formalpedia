-- Prove2me | solution 1 for OAI.Problem356.SmoothBranchMarginal.componentRegion_pairwise_of_subsets
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T22:14:46.97302+00:00
-- url     : https://prove2.me/submissions/13c85a70-a4cd-4a86-b518-b530e7983b95

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

open OAI OAI.Problem356 OAI.Problem356.SmoothBranchMarginal


theorem solution
    {B : Set E3} {e : Fin 4 → OpenPartialHomeomorph E3 E3}
    {U : Fin 5 → Set E3}
    (hU : Pairwise (fun i j => Disjoint (U i) (U j)))
    (hB : B ⊆ U 0) (he : ∀ i, e i '' B ⊆ U i.succ) :
    Pairwise (fun i j => Disjoint (componentRegion B e i) (componentRegion B e j)) := by
  let f : Option (Fin 4) → Fin 5 := fun i => match i with
    | none => 0
    | some k => k.succ
  have hf : Function.Injective f := by
    intro i j h
    rcases i with _ | i <;> rcases j with _ | j
    · rfl
    · exact absurd h.symm (Fin.succ_ne_zero j)
    · exact absurd h (Fin.succ_ne_zero i)
    · exact congrArg some (Fin.succ_injective _ h)
  have hsub : ∀ i, componentRegion B e i ⊆ U (f i) := by
    intro i
    rcases i with _ | i
    · exact hB
    · exact he i
  intro i j hij
  exact (hU (hf.ne hij)).mono (hsub i) (hsub j)

