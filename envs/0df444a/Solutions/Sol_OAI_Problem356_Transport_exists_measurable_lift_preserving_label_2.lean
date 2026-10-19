-- Prove2me | solution 2 for OAI.Problem356.Transport.exists_measurable_lift_preserving_label
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T21:37:24.483957+00:00
-- url     : https://prove2.me/submissions/5281f550-3ac5-4ae7-968b-b3b210c14950

-- Generated from openai/math@1581d4c lean/OAI/Analysis/CoulombTransport/CellwiseLift.lean:L17-L71
-- (upload_full_project.md Phase 4): solution for node OAI.Problem356.Transport.exists_measurable_lift_preserving_label. The node keeps its source
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
import Theorems.Thm_OAI_Problem356_PartitionTransport_exists_map_eq_sum_of_partition
import Theorems.Thm_OAI_Problem356_Transport_exists_measurable_transport_finite

-- ---- from OAI.Analysis.CoulombTransport.PartitionTransport ----
namespace OAI

universe uAlpha uBeta uIndex uKappa

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace Problem356.PartitionTransport

variable {α : Type uAlpha} {β : Type uBeta} {ι : Type uIndex} [MeasurableSpace α] [MeasurableSpace β]

/-- Prescribed laws on partition pieces can be glued into a transport to their sum. -/
theorem exists_map_eq_of_partition [Countable ι] [Nonempty ι]
    (μ : Measure α) (B : ι → Set α)
    (hB : ∀ i, MeasurableSet (B i))
    (hdisj : Pairwise fun i j => Disjoint (B i) (B j))
    (hcover : ∀ᵐ x ∂μ, x ∈ ⋃ i, B i)
    (T : ι → α → β) (hT : ∀ i, Measurable (T i))
    (ν : ι → Measure β)
    (hmap : ∀ i, Measure.map (T i) (μ.restrict (B i)) = ν i) :
    ∃ f : α → β, Measurable f ∧
      (∀ i, EqOn f (T i) (B i)) ∧ Measure.map f μ = Measure.sum ν := by
  obtain ⟨f, hf, hfg, hsum⟩ :=
    exists_map_eq_sum_of_partition μ B hB hdisj hcover T hT
  refine ⟨f, hf, hfg, ?_⟩
  simpa only [hmap] using hsum

end Problem356.PartitionTransport

end

end OAI

-- ---- from OAI.Analysis.CoulombTransport.CellwiseLift ----
namespace OAI

universe uX uY uIndex

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace Problem356.Transport

/-- A finite atomless source admits a lift to any finite law with that source as
marginal, while preserving any prescribed countable measurable label almost everywhere.
This permits cellwise approximation without splitting a three-index mass table. -/
theorem exists_measurable_lift_preserving_label
    {X : Type uX} {Y : Type uY} {ι : Type uIndex} [MeasurableSpace X] [StandardBorelSpace X]
    [MeasurableSpace Y] [StandardBorelSpace Y] [Nonempty Y]
    [MeasurableSpace ι] [MeasurableSingletonClass ι] [Countable ι] [Nonempty ι]
    (μ : Measure X) (ν : Measure Y) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    [NullSingletonClass μ] (f : Y → X) (hf : Measurable f)
    (hmarg : ν.map f = μ) (p : X → ι) (hp : Measurable p) :
    ∃ Q : X → Y, Measurable Q ∧ μ.map Q = ν ∧
      ∀ᵐ x ∂μ, p (f (Q x)) = p x := by
  classical
  let B : ι → Set X := fun i => p ⁻¹' {i}
  have hB (i : ι) : MeasurableSet (B i) := hp (measurableSet_singleton i)
  have hdisj : Pairwise fun i j => Disjoint (B i) (B j) := by
    intro i j hij
    apply Set.disjoint_left.mpr
    intro x hxi hxj
    exact hij (hxi.symm.trans hxj)
  have hcover : (⋃ i, B i) = univ := by
    ext x
    simp [B]
  have htransport (i : ι) : ∃ Q : X → Y, Measurable Q ∧
      (μ.restrict (B i)).map Q = ν.restrict (f ⁻¹' B i) := by
    apply exists_measurable_transport_finite
    simp only [Measure.restrict_apply_univ]
    rw [← hmarg, Measure.map_apply hf (hB i)]
  choose T hT hmap using htransport
  obtain ⟨Q, hQ, hQT, hQmap⟩ := PartitionTransport.exists_map_eq_of_partition
    μ B hB hdisj (by simp [hcover]) T hT
    (fun i => ν.restrict (f ⁻¹' B i)) hmap
  have hsum : Measure.sum (fun i => ν.restrict (f ⁻¹' B i)) = ν := by
    rw [← Measure.restrict_iUnion]
    · simp only [← preimage_iUnion, hcover, preimage_univ, Measure.restrict_univ]
    · intro i j hij
      exact (hdisj hij).preimage f
    · intro i
      exact (hB i).preimage hf
  refine ⟨Q, hQ, hQmap.trans hsum, ?_⟩
  have hlabel (i : ι) : ∀ᵐ x ∂μ.restrict (B i), p (f (T i x)) = i := by
    have hmem : ∀ᵐ x ∂μ.restrict (B i), f (T i x) ∈ B i := by
      apply ae_of_ae_map (μ := μ.restrict (B i)) (p := fun y => f y ∈ B i)
        (hT i).aemeasurable
      rw [hmap i]
      exact ae_restrict_mem ((hB i).preimage hf)
    exact hmem
  have hlabel' (i : ι) : ∀ᵐ x ∂μ, x ∈ B i → p (f (T i x)) = i :=
    (ae_restrict_iff' (hB i)).mp (hlabel i)
  have hall : ∀ᵐ x ∂μ, ∀ i, x ∈ B i → p (f (T i x)) = i :=
    ae_all_iff.mpr hlabel'
  filter_upwards [hall] with x hx
  have hxB : x ∈ B (p x) := rfl
  rw [hQT (p x) hxB]
  exact hx (p x) hxB

end Problem356.Transport

end

end OAI

-- ---- platform node ----
open OAI OAI.Problem356 OAI.Problem356.Transport
open MeasureTheory Set
open scoped ENNReal


theorem solution.{uX,uY,uIndex} : type_of% @_root_.OAI.Problem356.Transport.exists_measurable_lift_preserving_label.{uX,uY,uIndex} := @_root_.OAI.Problem356.Transport.exists_measurable_lift_preserving_label.{uX,uY,uIndex}
