-- Prove2me | solution 1 for OAI.Problem356.continuousAt_component_sum
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T20:55:49.041619+00:00
-- url     : https://prove2.me/submissions/78f3a112-8c98-416a-b684-9309ec384ad9

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

open OAI OAI.Problem356
universe uIndex
open Set Filter Metric
open scoped ENNReal BigOperators


theorem solution {ι : Type uIndex} (p : ι → E3) (v : ι → E3 → ℝ)
    (hv : ∀ i, ContinuousAt (v i) (p i)) (a : ι × (ι × ι)) :
    ContinuousAt
      (fun t : Triple => ENNReal.ofReal (v a.1 t.1 + v a.2.1 t.2.1 + v a.2.2 t.2.2))
      (p a.1, (p a.2.1, p a.2.2)) := by
  apply ENNReal.continuous_ofReal.continuousAt.comp
  have h1 : ContinuousAt (fun t : Triple => v a.1 t.1) (p a.1, (p a.2.1, p a.2.2)) :=
    (hv a.1).comp (f := fun t : Triple => t.1) continuous_fst.continuousAt
  have h2 : ContinuousAt (fun t : Triple => v a.2.1 t.2.1) (p a.1, (p a.2.1, p a.2.2)) :=
    (hv a.2.1).comp (f := fun t : Triple => t.2.1) (continuous_fst.comp continuous_snd).continuousAt
  have h3 : ContinuousAt (fun t : Triple => v a.2.2 t.2.2) (p a.1, (p a.2.1, p a.2.2)) :=
    (hv a.2.2).comp (f := fun t : Triple => t.2.2) (continuous_snd.comp continuous_snd).continuousAt
  exact (h1.add h2).add h3

