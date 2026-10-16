-- Prove2me | solution 1 for OAI.Problem310.gridBadCenters_period_subset
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T07:23:18.574363+00:00
-- url     : https://prove2.me/submissions/3b2e0e5c-35bf-4597-9045-10446869ef4b

-- Generated from openai/math@1581d4c lean/OAI/MeasureTheory/DyadicAvoidance/GridMeasure.lean:L51-L81
-- (upload_full_project.md Phase 4): solution for node OAI.Problem310.gridBadCenters_period_subset. The node keeps its source
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
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_PeriodicEnvelope
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_GlobalFromPeriodic
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_GridGeometry
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_GridMeasure

-- ---- from OAI.MeasureTheory.DyadicAvoidance.GridMeasure ----
namespace OAI

universe u_ι

noncomputable section
namespace Problem310
open MeasureTheory Set

theorem mem_gridBadCenters_iff (q : ℕ) (δ x : ℝ) :
    x ∈ gridBadCenters q δ ↔ ∃ k : ℤ, (k : ℝ) / q ∈ Ioc x (x + δ) := by
  simp only [gridBadCenters, mem_iUnion, mem_Ico, mem_Ioc]
  constructor
  · rintro ⟨k, hk⟩
    exact ⟨k, by linarith [hk.1], by linarith [hk.2]⟩
  · rintro ⟨k, hk⟩
    exact ⟨k, by linarith [hk.2], by linarith [hk.1]⟩

/-- Inside a half-open period the bad centers are covered by exactly `q`
intervals of length `δ`, provided `δ` is at most one cell width. -/
theorem gridBadCenters_period_subset (q : ℕ) (hq : 0 < q) {δ : ℝ}
    (hδ : δ ≤ (q : ℝ)⁻¹) :
    gridBadCenters q δ ∩ Ico (0 : ℝ) 1 ⊆
      ⋃ i : Fin q, Ico (((i.val + 1 : ℕ) : ℝ) / q - δ)
        (((i.val + 1 : ℕ) : ℝ) / q) := by
  intro x hx
  obtain ⟨k, hk⟩ := (mem_gridBadCenters_iff q δ x).mp hx.1
  have hqpos : (0 : ℝ) < q := by exact_mod_cast hq
  have hkpos : 0 < k := by
    have : (0 : ℝ) < (k : ℝ) / q := lt_of_le_of_lt hx.2.1 hk.1
    have := (div_pos_iff.mp this)
    exact_mod_cast (by rcases this with h | h; exact h.1; linarith [h.2] : (0 : ℝ) < k)
  have hklt : k < (q : ℤ) + 1 := by
    have hstep : (k : ℝ) / q < 1 + (q : ℝ)⁻¹ := by linarith [hx.2.2, hk.2]
    have hmul := (div_lt_iff₀ hqpos).mp hstep
    have hi : (q : ℝ)⁻¹ * q = 1 := inv_mul_cancel₀ hqpos.ne'
    have : (k : ℝ) < q + 1 := by nlinarith
    exact_mod_cast this
  have hkq : k.toNat ≤ q := by omega
  have hkn : 0 < k.toNat := by omega
  let i : Fin q := ⟨k.toNat - 1, by omega⟩
  apply mem_iUnion.mpr
  refine ⟨i, ?_⟩
  have hki : ((i.val + 1 : ℕ) : ℝ) = (k : ℝ) := by
    have : i.val + 1 = k.toNat := by dsimp [i]; omega
    rw [this]
    exact_mod_cast (Int.toNat_of_nonneg hkpos.le)
  rw [hki]
  exact ⟨by linarith [hk.2], hk.1⟩

end Problem310

end

end OAI

-- ---- platform node ----
open OAI OAI.Problem310
open MeasureTheory Set


theorem solution : type_of% @_root_.OAI.Problem310.gridBadCenters_period_subset := @_root_.OAI.Problem310.gridBadCenters_period_subset
