-- Prove2me | solution 1 for OAI.Problem310.Auxiliary.periodic_hitting_of_expected_exceptional
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T06:46:34.084891+00:00
-- url     : https://prove2.me/submissions/a54a30a1-7deb-4243-ae0c-48d661d539c8

-- Generated from openai/math@1581d4c lean/OAI/MeasureTheory/DyadicAvoidance/ExpectedRepair.lean:L14-L45
-- (upload_full_project.md Phase 4): solution for node OAI.Problem310.Auxiliary.periodic_hitting_of_expected_exceptional. The node keeps its source
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
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_CenterFailureBound
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_FirstDefault
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_ConcreteLabelMeasures
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_CenterFirstDefault
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_RandomSetDensity
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_RoutedSetDensity
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_RoutedExposure
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_FirstDefaultSelection
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_FiniteLocalPredicate
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_WindowData
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_WindowTableModel
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_StableRoutingBridge
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_WindowExceptionalTransfer
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_TrialAddresses
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_WindowTrialAddresses
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_ConcreteWindowAtom
import Theorems.Thm_OAI_Problem310_Auxiliary_repair_open_periodic_hitting

-- ---- from OAI.MeasureTheory.DyadicAvoidance.ExceptionalCenters ----
namespace OAI

noncomputable section

open Set Filter Topology

namespace Problem310.Auxiliary

section

open Set Filter Topology MeasureTheory Metric

end

open Set Filter Topology MeasureTheory

/-- The dyadic sequence converges to zero. -/
theorem dyadic_tendsto_zero :
    Tendsto (fun n : ℕ => (2 : ℝ)⁻¹ ^ n) atTop (𝓝 0) := by
  exact tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)

theorem periodic_hitting_of_small_exceptional
    (p : ℝ) (hp : 0 < p) (B : Set ℝ) (hBo : IsOpen B)
    (hBp : ∀ x : ℝ, x + 1 ∈ B ↔ x ∈ B)
    (N : Set ℕ) (hN : ∀ n ∈ N, 1 ≤ n)
    (hbound : volume (B ∩ Icc (0 : ℝ) 1) +
      volume (exceptionalCenters B N (fun n => (2 : ℝ)⁻¹ ^ n) ∩ Icc (0 : ℝ) 1)
        ≤ ENNReal.ofReal (5 * p)) :
    ∃ H : Set ℝ, IsOpen H ∧
      (∀ x : ℝ, x + 1 ∈ H ↔ x ∈ H) ∧
      volume (H ∩ Icc (0 : ℝ) 1) ≤ ENNReal.ofReal (6 * p) ∧
      ∀ x t : ℝ, t ∈ Icc (1 : ℝ) 2 →
        ∃ n : ℕ, 1 ≤ n ∧ x + t * ((2 : ℝ)⁻¹ ^ n) ∈ H := by
  obtain ⟨H, hHo, hHp, hHm, hHit⟩ := repair_open_periodic_hitting
    B hBo hBp N hN (fun n => (2 : ℝ)⁻¹ ^ n) dyadic_tendsto_zero
    (ENNReal.ofReal (5 * p)) hbound p hp
  refine ⟨H, hHo, hHp, ?_, hHit⟩
  convert hHm using 1
  rw [← ENNReal.ofReal_add (by positivity) (le_of_lt hp)]
  congr 1
  ring

end Problem310.Auxiliary

end

end OAI

-- ---- from OAI.MeasureTheory.DyadicAvoidance.ExpectedRepair ----
namespace OAI

universe u_Ω

noncomputable section

namespace Problem310.Auxiliary

open Set Filter Topology MeasureTheory

/-- First-moment selection followed by deterministic open-neighborhood repair. -/
theorem periodic_hitting_of_expected_exceptional
    {Ω : Type u_Ω} [Fintype Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (p : ℝ) (hp : 0 < p) (B : Ω → Set ℝ)
    (hBo : ∀ ω, IsOpen (B ω))
    (hBp : ∀ ω x, x + 1 ∈ B ω ↔ x ∈ B ω)
    (N : Set ℕ) (hN : ∀ n ∈ N, 1 ≤ n)
    (hBmean : (∫⁻ ω, volume (B ω ∩ Icc (0 : ℝ) 1) ∂μ) ≤ ENNReal.ofReal (2 * p))
    (hRmean : (∫⁻ ω, volume
      (exceptionalCenters (B ω) N (fun n => (2 : ℝ)⁻¹ ^ n) ∩ Icc (0 : ℝ) 1) ∂μ)
        ≤ ENNReal.ofReal (3 * p)) :
    ∃ H : Set ℝ, IsOpen H ∧
      (∀ x : ℝ, x + 1 ∈ H ↔ x ∈ H) ∧
      volume (H ∩ Icc (0 : ℝ) 1) ≤ ENNReal.ofReal (6 * p) ∧
      ∀ x t : ℝ, t ∈ Icc (1 : ℝ) 2 →
        ∃ n : ℕ, 1 ≤ n ∧ x + t * ((2 : ℝ)⁻¹ ^ n) ∈ H := by
  let f : Ω → ENNReal := fun ω => volume (B ω ∩ Icc (0 : ℝ) 1)
  let g : Ω → ENNReal := fun ω => volume
    (exceptionalCenters (B ω) N (fun n => (2 : ℝ)⁻¹ ^ n) ∩ Icc (0 : ℝ) 1)
  have hf : Measurable f := measurable_of_countable f
  have hg : Measurable g := measurable_of_countable g
  obtain ⟨ω, hω⟩ := exists_le_lintegral (μ := μ) (hf.add hg).aemeasurable
  apply periodic_hitting_of_small_exceptional p hp (B ω) (hBo ω) (hBp ω) N hN
  calc
    f ω + g ω ≤ ∫⁻ ω, f ω + g ω ∂μ := hω
    _ = (∫⁻ ω, f ω ∂μ) + ∫⁻ ω, g ω ∂μ := lintegral_add_left hf _
    _ ≤ ENNReal.ofReal (2 * p) + ENNReal.ofReal (3 * p) := add_le_add hBmean hRmean
    _ = ENNReal.ofReal (5 * p) := by
      rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
      congr 1
      ring

end Problem310.Auxiliary

end

end OAI

-- ---- platform node ----
open OAI OAI.Problem310 OAI.Problem310.Auxiliary
open Set Filter Topology MeasureTheory


theorem solution.{u_Ω} : type_of% @_root_.OAI.Problem310.Auxiliary.periodic_hitting_of_expected_exceptional.{u_Ω} := @_root_.OAI.Problem310.Auxiliary.periodic_hitting_of_expected_exceptional.{u_Ω}
