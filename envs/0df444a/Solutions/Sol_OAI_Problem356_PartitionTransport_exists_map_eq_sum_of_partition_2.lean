-- Prove2me | solution 2 for OAI.Problem356.PartitionTransport.exists_map_eq_sum_of_partition
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T21:33:00.542712+00:00
-- url     : https://prove2.me/submissions/ad7b4ae5-2924-42c9-b1f6-d100c2fbc724

-- Generated from openai/math@1581d4c lean/OAI/Analysis/CoulombTransport/PartitionTransport.lean:L16-L43
-- (upload_full_project.md Phase 4): solution for node OAI.Problem356.PartitionTransport.exists_map_eq_sum_of_partition. The node keeps its source
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

-- ---- from OAI.Analysis.CoulombTransport.PartitionTransport ----
namespace OAI

universe uAlpha uBeta uIndex uKappa

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace Problem356.PartitionTransport

variable {α : Type uAlpha} {β : Type uBeta} {ι : Type uIndex} [MeasurableSpace α] [MeasurableSpace β]

/-- Gluing measurable transports on a countable measurable partition gives the
sum of their restricted pushforwards. The partition need only cover almost everywhere. -/
theorem exists_map_eq_sum_of_partition [Countable ι] [Nonempty ι]
    (μ : Measure α) (B : ι → Set α)
    (hB : ∀ i, MeasurableSet (B i))
    (hdisj : Pairwise fun i j => Disjoint (B i) (B j))
    (hcover : ∀ᵐ x ∂μ, x ∈ ⋃ i, B i)
    (T : ι → α → β) (hT : ∀ i, Measurable (T i)) :
    ∃ f : α → β, Measurable f ∧
      (∀ i, EqOn f (T i) (B i)) ∧
      Measure.map f μ = Measure.sum (fun i => Measure.map (T i) (μ.restrict (B i))) := by
  obtain ⟨f, hf, hfg⟩ := exists_measurable_piecewise B hB T hT (by
    intro i j hij x hx
    exact False.elim (Set.disjoint_left.mp (hdisj hij) hx.1 hx.2))
  refine ⟨f, hf, hfg, ?_⟩
  have hdecomp : μ = Measure.sum (fun i => μ.restrict (B i)) := by
    rw [← Measure.restrict_iUnion hdisj hB, Measure.restrict_eq_self_of_ae_mem hcover]
  calc
    Measure.map f μ = Measure.map f (Measure.sum (fun i => μ.restrict (B i))) :=
      congrArg (Measure.map f) hdecomp
    _ = Measure.sum (fun i => Measure.map f (μ.restrict (B i))) :=
      Measure.map_sum hf.aemeasurable
    _ = _ := by
      congr 1
      funext i
      apply Measure.map_congr
      filter_upwards [ae_restrict_mem (hB i)] with x hx
      exact hfg i hx

end Problem356.PartitionTransport

end

end OAI

-- ---- platform node ----
open OAI OAI.Problem356 OAI.Problem356.PartitionTransport
open MeasureTheory Set
open scoped ENNReal


theorem solution.{uAlpha,uBeta,uIndex} : type_of% @_root_.OAI.Problem356.PartitionTransport.exists_map_eq_sum_of_partition.{uAlpha,uBeta,uIndex} := @_root_.OAI.Problem356.PartitionTransport.exists_map_eq_sum_of_partition.{uAlpha,uBeta,uIndex}
