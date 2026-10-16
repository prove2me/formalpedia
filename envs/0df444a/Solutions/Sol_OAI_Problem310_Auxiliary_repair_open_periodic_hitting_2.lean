-- Prove2me | solution 2 for OAI.Problem310.Auxiliary.repair_open_periodic_hitting
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T05:49:59.066678+00:00
-- url     : https://prove2.me/submissions/8ffb8875-6b2b-4a42-8108-4ae660fe97c2

-- Generated from openai/math@1581d4c lean/OAI/MeasureTheory/DyadicAvoidance/ExceptionalCenters.lean:L133-L167
-- (upload_full_project.md Phase 4): solution for node OAI.Problem310.Auxiliary.repair_open_periodic_hitting. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_DyadicAvoidance
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_PeriodicBasic
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_GridSeparation
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_FiniteTableModel
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_OrderedRouting
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_RoutingPath
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_CenterRouteExposure
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_ExceptionalCenters
import Theorems.Thm_OAI_Problem310_Auxiliary_exceptionalCenters_periodic
import Theorems.Thm_OAI_Problem310_Auxiliary_exists_open_periodic_superset
import Theorems.Thm_OAI_Problem310_Auxiliary_isClosed_exceptionalCenters

-- ---- from OAI.MeasureTheory.DyadicAvoidance.ExceptionalCenters ----
namespace OAI

noncomputable section

open Set Filter Topology

namespace Problem310.Auxiliary

section

/-- An open neighborhood of a limit point meets every tail of a converging sequence. -/
theorem exists_tail_mem_of_tendsto (a : ℕ → ℝ) (ha : Tendsto a atTop (𝓝 0))
    (V : Set ℝ) (hV : IsOpen V) (x : ℝ) (hx : x ∈ V) (t : ℝ) :
    ∃ n : ℕ, 1 ≤ n ∧ x + t * a n ∈ V := by
  have hlim : Tendsto (fun n => x + t * a n) atTop (𝓝 x) := by
    simpa using tendsto_const_nhds.add (tendsto_const_nhds.mul ha)
  have hev : ∀ᶠ n in atTop, x + t * a n ∈ V := hlim.eventually (hV.mem_nhds hx)
  obtain ⟨n, hn, hmem⟩ := (eventually_ge_atTop 1 |>.and hev).exists
  exact ⟨n, hn, hmem⟩

/-- Open-neighborhood repair turns tests away from exceptional centers into hits everywhere. -/
theorem exceptionalCenters_repair (B V : Set ℝ) (N : Set ℕ) (a : ℕ → ℝ)
    (ha : Tendsto a atTop (𝓝 0)) (hN : ∀ n ∈ N, 1 ≤ n)
    (hV : IsOpen V) (hcover : exceptionalCenters B N a ⊆ V) :
    ∀ x t : ℝ, t ∈ Icc (1 : ℝ) 2 →
      ∃ n : ℕ, 1 ≤ n ∧ x + t * a n ∈ B ∪ V := by
  intro x t ht
  by_cases hx : x ∈ exceptionalCenters B N a
  · obtain ⟨n, hn, hmem⟩ := exists_tail_mem_of_tendsto a ha V hV x (hcover hx) t
    exact ⟨n, hn, Or.inr hmem⟩
  · have htest : ∃ n ∈ N, x + t * a n ∈ B := by
      by_contra! h
      exact hx ⟨t, ht, h⟩
    obtain ⟨n, hn, hmem⟩ := htest
    exact ⟨n, hN n hn, Or.inl hmem⟩

open Set Filter Topology MeasureTheory Metric

end

open Set Filter Topology MeasureTheory

/-- Deterministic completion of the probabilistic construction: once the density of
an open test set plus its exceptional centers is small, a genuinely hitting open
periodic set is available at arbitrarily small additional density cost. -/
theorem repair_open_periodic_hitting
    (B : Set ℝ) (hBo : IsOpen B)
    (hBp : ∀ x : ℝ, x + 1 ∈ B ↔ x ∈ B)
    (N : Set ℕ) (hN : ∀ n ∈ N, 1 ≤ n)
    (a : ℕ → ℝ) (ha : Tendsto a atTop (𝓝 0))
    (c : ENNReal)
    (hbound : volume (B ∩ Icc (0 : ℝ) 1) +
      volume (exceptionalCenters B N a ∩ Icc (0 : ℝ) 1) ≤ c)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ H : Set ℝ, IsOpen H ∧
      (∀ x : ℝ, x + 1 ∈ H ↔ x ∈ H) ∧
      volume (H ∩ Icc (0 : ℝ) 1) ≤ c + ENNReal.ofReal ε ∧
      ∀ x t : ℝ, t ∈ Icc (1 : ℝ) 2 →
        ∃ n : ℕ, 1 ≤ n ∧ x + t * a n ∈ H := by
  obtain ⟨V, hVo, hVp, hRV, hVm⟩ := exists_open_periodic_superset
    (exceptionalCenters B N a) (isClosed_exceptionalCenters B hBo N a)
    (exceptionalCenters_periodic B hBp N a) ε hε
  refine ⟨B ∪ V, hBo.union hVo, ?_, ?_,
    exceptionalCenters_repair B V N a ha hN hVo hRV⟩
  · intro x
    simp only [mem_union, hBp, hVp]
  · calc
      volume ((B ∪ V) ∩ Icc (0 : ℝ) 1)
          ≤ volume (B ∩ Icc (0 : ℝ) 1) + volume (V ∩ Icc (0 : ℝ) 1) := by
            rw [union_inter_distrib_right]
            exact measure_union_le _ _
      _ ≤ volume (B ∩ Icc (0 : ℝ) 1) +
          (volume (exceptionalCenters B N a ∩ Icc (0 : ℝ) 1) +
            ENNReal.ofReal ε) := add_le_add le_rfl hVm
      _ ≤ c + ENNReal.ofReal ε := by
        rw [← add_assoc]
        exact add_le_add hbound le_rfl

end Problem310.Auxiliary

end

end OAI

-- ---- platform node ----
open OAI OAI.Problem310 OAI.Problem310.Auxiliary
open Set Filter Topology
open Set Filter Topology MeasureTheory


theorem solution : type_of% @_root_.OAI.Problem310.Auxiliary.repair_open_periodic_hitting := @_root_.OAI.Problem310.Auxiliary.repair_open_periodic_hitting
