-- Prove2me | solution 2 for OAI.Problem356.continuousAt_component_sum
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T21:50:34.283795+00:00
-- url     : https://prove2.me/submissions/afc4a216-9911-4bc6-8156-8539e5f5ddca

-- Generated from openai/math@1581d4c lean/OAI/Analysis/CoulombTransport/ComponentCertificate.lean:L49-L66
-- (upload_full_project.md Phase 4): solution for node OAI.Problem356.continuousAt_component_sum. The node keeps its source
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

-- ---- from OAI.Analysis.CoulombTransport.ComponentCertificate ----
namespace OAI

universe uIndex

noncomputable section
open Set Filter Metric
open scoped ENNReal BigOperators

namespace Problem356

/-- Continuity of the sum of the three local potentials in one component type. -/
theorem continuousAt_component_sum {ι : Type uIndex} (p : ι → E3) (v : ι → E3 → ℝ)
    (hv : ∀ i, ContinuousAt (v i) (p i)) (a : ι × (ι × ι)) :
    ContinuousAt
      (fun t : Triple => ENNReal.ofReal (v a.1 t.1 + v a.2.1 t.2.1 + v a.2.2 t.2.2))
      (p a.1, (p a.2.1, p a.2.2)) := by
  have h₁ : ContinuousAt (fun t : Triple => v a.1 t.1)
      (p a.1, (p a.2.1, p a.2.2)) :=
    (hv a.1).comp (f := fun t : Triple => t.1) continuousAt_fst
  have h₂ : ContinuousAt (fun t : Triple => v a.2.1 t.2.1)
      (p a.1, (p a.2.1, p a.2.2)) :=
    (hv a.2.1).comp (f := fun t : Triple => t.2.1)
      (continuousAt_fst.comp continuousAt_snd)
  have h₃ : ContinuousAt (fun t : Triple => v a.2.2 t.2.2)
      (p a.1, (p a.2.1, p a.2.2)) :=
    (hv a.2.2).comp (f := fun t : Triple => t.2.2)
      (continuousAt_snd.comp continuousAt_snd)
  exact ENNReal.continuous_ofReal.continuousAt.comp ((h₁.add h₂).add h₃)

end Problem356

end

end OAI

-- ---- platform node ----
open OAI OAI.Problem356
open Set Filter Metric
open scoped ENNReal BigOperators


theorem solution.{uIndex} : type_of% @_root_.OAI.Problem356.continuousAt_component_sum.{uIndex} := @_root_.OAI.Problem356.continuousAt_component_sum.{uIndex}
