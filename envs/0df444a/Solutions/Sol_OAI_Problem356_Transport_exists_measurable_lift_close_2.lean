-- Prove2me | solution 2 for OAI.Problem356.Transport.exists_measurable_lift_close
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T21:38:47.025357+00:00
-- url     : https://prove2.me/submissions/6afb6f00-9f25-4624-a3a2-3eb2a3dd9a30

-- Generated from openai/math@1581d4c lean/OAI/Analysis/CoulombTransport/CellwiseLift.lean:L73-L99
-- (upload_full_project.md Phase 4): solution for node OAI.Problem356.Transport.exists_measurable_lift_close. The node keeps its source
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
import Theorems.Thm_OAI_Problem356_FiniteCells_cellLabel_eq_some_iff
import Theorems.Thm_OAI_Problem356_Transport_exists_measurable_lift_preserving_label
import Theorems.Thm_OAI_Problem356_exists_compact_small_partition

-- ---- from OAI.Analysis.CoulombTransport.PartitionLabel ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem dite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α} {e : ¬c → α} : (dite c t e) = t hc := @dif_pos c h hc α t e
private theorem dite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t : c → α} {e : ¬c → α} : (dite c t e) = e hc := @dif_neg c h hc α t e

namespace OAI

universe uX uIndex

noncomputable section

open Set MeasureTheory

namespace Problem356.FiniteCells

lemma cellLabel_eq_none_iff {X : Type uX} {ι : Type uIndex} (A : ι → Set X) (x : X) :
    cellLabel A x = none ↔ x ∉ ⋃ i, A i := by
  classical
  by_cases h : ∃ i, x ∈ A i
  · simp only [cellLabel, dite_eq_left h, reduceCtorEq, false_iff, not_not]
    exact mem_iUnion.mpr h
  · simp only [cellLabel, dite_eq_right h, true_iff]
    exact fun hx => h (mem_iUnion.mp hx)

lemma cellLabel_fiber_some {X : Type uX} {ι : Type uIndex} {A : ι → Set X}
    (hDisjoint : Pairwise (fun i j => Disjoint (A i) (A j))) (i : ι) :
    cellLabel A ⁻¹' {some i} = A i := by
  ext x
  exact cellLabel_eq_some_iff hDisjoint x i

lemma cellLabel_fiber_none {X : Type uX} {ι : Type uIndex} (A : ι → Set X) :
    cellLabel A ⁻¹' {none} = (⋃ i, A i)ᶜ := by
  ext x
  exact cellLabel_eq_none_iff A x

lemma measurable_cellLabel {X : Type uX} {ι : Type uIndex} [MeasurableSpace X]
    [MeasurableSpace (Option ι)] [Countable ι] {A : ι → Set X}
    (hA : ∀ i, MeasurableSet (A i))
    (hDisjoint : Pairwise (fun i j => Disjoint (A i) (A j))) :
    Measurable (cellLabel A) := by
  apply measurable_to_countable'
  intro i
  cases i with
  | none =>
      rw [cellLabel_fiber_none]
      exact (MeasurableSet.iUnion hA).compl
  | some i =>
      rw [cellLabel_fiber_some hDisjoint]
      exact hA i

end Problem356.FiniteCells

end

end OAI

-- ---- from OAI.Analysis.CoulombTransport.CellwiseLift ----
namespace OAI

universe uX uY uIndex

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace Problem356.Transport

/-- A lift can preserve the source coordinate to arbitrary precision whenever
that source has compact support. Only the first marginal is approximated; the
entire target law is transported exactly. -/
theorem exists_measurable_lift_close
    {X : Type uX} {Y : Type uY} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    [StandardBorelSpace X] [MeasurableSpace Y] [StandardBorelSpace Y] [Nonempty Y]
    (μ : Measure X) (ν : Measure Y) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    [NullSingletonClass μ] (f : Y → X) (hf : Measurable f) (hmarg : ν.map f = μ)
    {K : Set X} (hK : IsCompact K) (hfull : μ Kᶜ = 0)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ Q : X → Y, Measurable Q ∧ μ.map Q = ν ∧
      ∀ᵐ x ∂μ, dist x (f (Q x)) < δ := by
  obtain ⟨n, A, hA, hdisj, hcover, _, hdiam⟩ := exists_compact_small_partition hK hδ
  let : MeasurableSpace (Option (Fin n)) := ⊤
  obtain ⟨Q, hQ, hmap, hlabel⟩ := exists_measurable_lift_preserving_label
    μ ν f hf hmarg (FiniteCells.cellLabel A) (FiniteCells.measurable_cellLabel hA hdisj)
  refine ⟨Q, hQ, hmap, ?_⟩
  have hxK : ∀ᵐ x ∂μ, x ∈ K := ae_iff.mpr hfull
  filter_upwards [hlabel, hxK] with x hx hxK
  have hxA : x ∈ ⋃ i, A i := by rwa [hcover]
  obtain ⟨i, hi⟩ := mem_iUnion.mp hxA
  have hlabelx : FiniteCells.cellLabel A x = some i :=
    (FiniteCells.cellLabel_eq_some_iff hdisj x i).mpr hi
  have hlabelQ : FiniteCells.cellLabel A (f (Q x)) = some i := hx.trans hlabelx
  have hQi : f (Q x) ∈ A i :=
    (FiniteCells.cellLabel_eq_some_iff hdisj (f (Q x)) i).mp hlabelQ
  exact hdiam i x hi (f (Q x)) hQi

end Problem356.Transport

end

end OAI

-- ---- platform node ----
open OAI OAI.Problem356 OAI.Problem356.Transport
open MeasureTheory Set
open scoped ENNReal


theorem solution.{uX,uY} : type_of% @_root_.OAI.Problem356.Transport.exists_measurable_lift_close.{uX,uY} := @_root_.OAI.Problem356.Transport.exists_measurable_lift_close.{uX,uY}
