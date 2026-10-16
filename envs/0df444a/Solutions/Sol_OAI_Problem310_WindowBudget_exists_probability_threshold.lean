-- Prove2me | solution 1 for OAI.Problem310.WindowBudget.exists_probability_threshold
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T06:56:23.062862+00:00
-- url     : https://prove2.me/submissions/cb3e2706-88b8-4afe-aee5-c237ba73cc16

-- Generated from openai/math@1581d4c lean/OAI/MeasureTheory/DyadicAvoidance/WindowBudgets.lean:L122-L141
-- (upload_full_project.md Phase 4): solution for node OAI.Problem310.WindowBudget.exists_probability_threshold. The node keeps its source
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
import Theorems.Thm_OAI_Problem310_WindowBudget_entropy_tendsto_zero

-- ---- from OAI.MeasureTheory.DyadicAvoidance.WindowBudgets ----
namespace OAI

noncomputable section

open Filter
open scoped Topology

namespace Problem310.WindowBudget

/-- A single lower bound on the window length works for every larger window. -/
lemma exists_entropy_threshold (p M a : ℝ) (hp : 0 < p) (ha : 10 ≤ a) :
    ∃ r₀ : ℕ, 1 ≤ r₀ ∧ ∀ r : ℕ, r₀ ≤ r →
      20 * M * (r : ℝ) * (1 + (2 : ℝ) ^ (2 * r + 2)) *
        Real.exp (-a * (r : ℝ)) < p := by
  have h := (entropy_tendsto_zero M a ha).eventually_lt_const hp
  obtain ⟨r₀, hr₀⟩ := eventually_atTop.mp h
  refine ⟨max 1 r₀, le_max_left _ _, ?_⟩
  intro r hr
  exact hr₀ r ((le_max_right _ _).trans hr)

/-- The elementary Bernoulli miss probability is bounded by an exponential. -/
lemma one_sub_pow_le_exp (u : ℝ) (hu : u ≤ 1) (N : ℕ) :
    (1 - u) ^ N ≤ Real.exp (-u * (N : ℝ)) := by
  have hbase : 1 - u ≤ Real.exp (-u) := by
    have h := Real.add_one_le_exp (-u)
    linarith
  calc
    (1 - u) ^ N ≤ Real.exp (-u) ^ N :=
      pow_le_pow_left₀ (by linarith) hbase N
    _ = Real.exp (-u * (N : ℝ)) := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring

/-- The window threshold also bounds the actual fixed-scale failure probability
multiplied by the number of scale representatives. -/
lemma exists_probability_threshold (p : ℝ) (hp : 0 < p) (hp1 : p < 1)
    (M : ℕ) (hM : 2 ≤ M) (hmargin : 10 ≤ p * ((M : ℝ) - 1) / 2) :
    ∃ r₀ : ℕ, 1 ≤ r₀ ∧ ∀ r : ℕ, r₀ ≤ r →
      20 * (M : ℝ) * (r : ℝ) * (1 + (2 : ℝ) ^ (2 * r + 2)) *
        (1 - p / 2) ^ ((M - 1) * r) < p := by
  obtain ⟨r₀, hr₀, hsmall⟩ :=
    exists_entropy_threshold p M (p * ((M : ℝ) - 1) / 2) hp hmargin
  refine ⟨r₀, hr₀, ?_⟩
  intro r hr
  have hpow := one_sub_pow_le_exp (p / 2) (by linarith) ((M - 1) * r)
  have hexp : -(p / 2) * (((M - 1) * r : ℕ) : ℝ) =
      -(p * ((M : ℝ) - 1) / 2) * (r : ℝ) := by
    rw [Nat.cast_mul, Nat.cast_sub (by omega : 1 ≤ M)]
    push_cast
    ring
  rw [hexp] at hpow
  exact lt_of_le_of_lt
    (mul_le_mul_of_nonneg_left hpow (by positivity)) (hsmall r hr)

end Problem310.WindowBudget

end

end OAI

-- ---- platform node ----
open OAI OAI.Problem310 OAI.Problem310.WindowBudget
open Filter
open scoped Topology


theorem solution : type_of% @_root_.OAI.Problem310.WindowBudget.exists_probability_threshold := @_root_.OAI.Problem310.WindowBudget.exists_probability_threshold
