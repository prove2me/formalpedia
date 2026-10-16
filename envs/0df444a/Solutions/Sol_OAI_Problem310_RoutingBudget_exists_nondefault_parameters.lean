-- Prove2me | solution 1 for OAI.Problem310.RoutingBudget.exists_nondefault_parameters
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T06:58:07.272884+00:00
-- url     : https://prove2.me/submissions/299c000e-1a6a-431e-ba3f-ad65fe233418

-- Generated from openai/math@1581d4c lean/OAI/MeasureTheory/DyadicAvoidance/RoutingBudget.lean:L18-L51
-- (upload_full_project.md Phase 4): solution for node OAI.Problem310.RoutingBudget.exists_nondefault_parameters. The node keeps its source
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
import Theorems.Thm_OAI_Problem310_WindowBudget_exists_probability_threshold

-- ---- from OAI.MeasureTheory.DyadicAvoidance.MonotoneRepresentatives ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe u_α u_ι

noncomputable section

open scoped BigOperators

namespace Problem310.ScaleDiscretization

/-- The stronger monotone-key estimate is within the entropy budget. -/
lemma representative_card_budget (M r D : ℕ) (hM : 1 ≤ M) (hr : 1 ≤ r) :
    1 + (M - 1) * r * D ≤ 20 * M * r * (1 + D) := by
  have hMr : 1 ≤ M * r := by nlinarith
  calc
    1 + (M - 1) * r * D ≤ M * r + M * r * D := by
      exact Nat.add_le_add hMr
        (Nat.mul_le_mul_right D (Nat.mul_le_mul_right r (Nat.sub_le M 1)))
    _ = M * r * (1 + D) := by ring
    _ ≤ 20 * M * r * (1 + D) := by nlinarith

end Problem310.ScaleDiscretization

end

end OAI

-- ---- from OAI.MeasureTheory.DyadicAvoidance.WindowBudgets ----
namespace OAI

noncomputable section

open Filter
open scoped Topology

namespace Problem310.WindowBudget

/-- Choose the branching number with the required exponential margin. -/
lemma exists_branching_number (p : ℝ) (hp : 0 < p) :
    ∃ M : ℕ, 2 ≤ M ∧ 10 ≤ p * ((M : ℝ) - 1) / 2 := by
  obtain ⟨N, hN⟩ := exists_nat_gt (20 / p)
  have hprod : 20 < (N : ℝ) * p := (div_lt_iff₀ hp).mp hN
  refine ⟨N + 2, by omega, ?_⟩
  push_cast
  nlinarith

/-- A geometric probability can be made arbitrarily small at a positive depth. -/
lemma exists_positive_depth (p q : ℝ) (hp : 0 < p) (hq0 : 0 ≤ q) (hq1 : q < 1) :
    ∃ d : ℕ, 1 ≤ d ∧ q ^ d < p := by
  have h := (tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1).eventually_lt_const hp
  obtain ⟨d, hd⟩ := eventually_atTop.mp h
  exact ⟨max 1 d, le_max_left _ _, hd _ (le_max_right _ _)⟩

/-- The branching factor and tree depth can be chosen in the prescribed order. -/
lemma exists_tree_parameters (p : ℝ) (hp : 0 < p) :
    ∃ M d : ℕ, 2 ≤ M ∧ 1 ≤ d ∧
      10 ≤ p * ((M : ℝ) - 1) / 2 ∧
      (1 - ((2 : ℝ)⁻¹) ^ (M - 1)) ^ d < p := by
  obtain ⟨M, hM, hmargin⟩ := exists_branching_number p hp
  have hpowpos : (0 : ℝ) < ((2 : ℝ)⁻¹) ^ (M - 1) := by positivity
  have hpowle : ((2 : ℝ)⁻¹) ^ (M - 1) ≤ (1 : ℝ) := by
    exact pow_le_one₀ (by norm_num) (by norm_num)
  obtain ⟨d, hd, hsmall⟩ := exists_positive_depth p
    (1 - ((2 : ℝ)⁻¹) ^ (M - 1)) hp (by linarith) (by linarith)
  exact ⟨M, d, hM, hd, hmargin, hsmall⟩

end Problem310.WindowBudget

end

end OAI

-- ---- from OAI.MeasureTheory.DyadicAvoidance.RoutingBudget ----
namespace OAI

noncomputable section

namespace Problem310.RoutingBudget

/-- Transfer a real finite-union estimate to the extended-nonnegative probability scale. -/
lemma ennreal_card_mul_pow_lt {p q : ℝ} (hp : 0 < p) (hq : 0 ≤ q)
    (N k : ℕ) (h : (N : ℝ) * q ^ k < p) :
    (N : ENNReal) * (ENNReal.ofReal q) ^ k < ENNReal.ofReal p := by
  have he := (ENNReal.ofReal_lt_ofReal_iff hp).2 h
  simpa only [ENNReal.ofReal_mul (Nat.cast_nonneg N), ENNReal.ofReal_natCast,
    ENNReal.ofReal_pow hq] using he

/-- Choose parameters in the router convention: `M` is the number of nondefault
children, so there are `M + 1` children altogether. The last estimate is ready for
an `ENNReal` finite union bound over the monotone-key representatives. -/
theorem exists_nondefault_parameters (p : ℝ) (hp : 0 < p) (hp1 : p < 1) :
    ∃ M d R : ℕ, 1 ≤ M ∧ 1 ≤ d ∧ 1 ≤ R ∧
      10 ≤ p * (M : ℝ) / 2 ∧
      (1 - ((2 : ℝ)⁻¹) ^ M) ^ d < p ∧
      ∀ r : ℕ, R ≤ r → ∀ N : ℕ,
        N ≤ 1 + M * r * 2 ^ (2 * r + 2) →
        (N : ENNReal) * (ENNReal.ofReal (1 - p / 2)) ^ (M * r) <
          ENNReal.ofReal p := by
  obtain ⟨T, d, hT, hd, hmargin, hdepth⟩ :=
    WindowBudget.exists_tree_parameters p hp
  obtain ⟨M, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : T ≠ 0)
  obtain ⟨R, hR, hsmall⟩ :=
    WindowBudget.exists_probability_threshold p hp hp1 (M + 1) hT hmargin
  have hM : 1 ≤ M := by omega
  have hmargin' : 10 ≤ p * (M : ℝ) / 2 := by
    simpa only [Nat.cast_succ, add_sub_cancel_right] using hmargin
  simp only [Nat.add_sub_cancel] at hdepth hsmall
  refine ⟨M, d, R, hM, hd, hR, hmargin', hdepth, ?_⟩
  intro r hr N hN
  have hrpos : 1 ≤ r := hR.trans hr
  have hcard := ScaleDiscretization.representative_card_budget
    (M + 1) r (2 ^ (2 * r + 2)) (by omega) hrpos
  simp only [Nat.add_sub_cancel] at hcard
  have hNbig : N ≤ 20 * (M + 1) * r * (1 + 2 ^ (2 * r + 2)) :=
    hN.trans hcard
  have hNreal : (N : ℝ) ≤ 20 * ((M + 1 : ℕ) : ℝ) * (r : ℝ) *
      (1 + (2 : ℝ) ^ (2 * r + 2)) := by
    exact_mod_cast hNbig
  apply ennreal_card_mul_pow_lt hp (by linarith) N (M * r)
  exact (mul_le_mul_of_nonneg_right hNreal (pow_nonneg (by linarith) _)).trans_lt
    (hsmall r hr)

end Problem310.RoutingBudget

end

end OAI

-- ---- platform node ----
open OAI OAI.Problem310 OAI.Problem310.RoutingBudget


theorem solution : type_of% @_root_.OAI.Problem310.RoutingBudget.exists_nondefault_parameters := @_root_.OAI.Problem310.RoutingBudget.exists_nondefault_parameters
