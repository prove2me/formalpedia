-- Prove2me | solution 1 for MeasurableSelection.exists_selection_of_denseRange
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:14:03.56628+00:00
-- url     : https://prove2.me/submissions/43d4b21d-8bb2-4d59-b464-f44dcf76d34b

import Mathlib
import Definitions.Def_BicausalOT_DescriptiveSetTheory_MeasurableSelection
import Theorems.Thm_MeasurableSelection_approxFun_close
import Theorems.Thm_MeasurableSelection_approxFun_dist_succ
import Theorems.Thm_MeasurableSelection_approxFun_measurable

set_option autoImplicit false
open Metric Set Filter Topology TopologicalSpace
open MeasurableSelection
variable {α : Type*} [MeasurableSpace α]
variable {Y : Type*} [MetricSpace Y] {Φ : α → Set Y} {u : ℕ → Y}
variable [MeasurableSpace Y] [BorelSpace Y]
namespace MeasurableSelection
theorem _root_.solution [CompleteSpace Y]
    (hu : DenseRange u) (hne : ∀ a, (Φ a).Nonempty) (hclosed : ∀ a, IsClosed (Φ a))
    (hΦ : ∀ U : Set Y, IsOpen U → MeasurableSet {a | (Φ a ∩ U).Nonempty}) :
    ∃ f : α → Y, Measurable f ∧ ∀ a, f a ∈ Φ a := by
  have hcauchy : ∀ a, CauchySeq fun n => approxFun hu hne hΦ n a := fun a =>
    cauchySeq_of_le_geometric (1 / 2) (3 / 2) (by norm_num)
      (fun n => approxFun_dist_succ hu hne hΦ n a)
  choose f hf using fun a => cauchySeq_tendsto_of_complete (hcauchy a)
  refine ⟨f, ?_, ?_⟩
  · exact measurable_of_tendsto_metrizable (fun n => approxFun_measurable hu hne hΦ n)
      (tendsto_pi_nhds.mpr hf)
  · intro a
    rw [← (hclosed a).closure_eq, Metric.mem_closure_iff]
    intro ε hε
    have h1 : ∀ᶠ n in atTop, dist (approxFun hu hne hΦ n a) (f a) < ε / 2 := by
      obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp (hf a) (ε / 2) (half_pos hε)
      exact eventually_atTop.mpr ⟨N, hN⟩
    have h2 : ∀ᶠ n : ℕ in atTop, (1 / 2 : ℝ) ^ n < ε / 2 :=
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)).eventually_lt_const
        (half_pos hε)
    obtain ⟨n, hn1, hn2⟩ := (h1.and h2).exists
    obtain ⟨y, hyΦ, hyb⟩ := approxFun_close hu hne hΦ n a
    refine ⟨y, hyΦ, ?_⟩
    calc dist (f a) y ≤
        dist (f a) (approxFun hu hne hΦ n a) + dist (approxFun hu hne hΦ n a) y :=
          dist_triangle _ _ _
      _ < ε / 2 + ε / 2 :=
          add_lt_add (by rw [dist_comm]; exact hn1) ((mem_ball'.mp hyb).trans hn2)
      _ = ε := by ring
end MeasurableSelection
