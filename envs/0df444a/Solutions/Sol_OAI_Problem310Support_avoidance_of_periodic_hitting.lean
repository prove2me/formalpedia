-- Prove2me | solution 1 for OAI.Problem310Support.avoidance_of_periodic_hitting
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T07:15:49.954285+00:00
-- url     : https://prove2.me/submissions/2c9048e1-bd58-44e7-89cf-3c8289a61c38

-- Generated from openai/math@1581d4c lean/OAI/MeasureTheory/DyadicAvoidance/GlobalFromPeriodic.lean:L147-L185
-- (upload_full_project.md Phase 4): solution for node OAI.Problem310Support.avoidance_of_periodic_hitting. The node keeps its source
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
import Theorems.Thm_OAI_Problem310Support_compact_complement_volume
import Theorems.Thm_OAI_Problem310Support_periodic_dilate_unit_volume_le
import Theorems.Thm_OAI_Problem310Support_periodic_reflect_unit_volume
import Theorems.Thm_OAI_Problem310Support_signedDyadicUnion_hits

-- ---- from OAI.MeasureTheory.DyadicAvoidance.PeriodicMeasure ----
namespace OAI

noncomputable section

open Set MeasureTheory

namespace Problem310Support

/-- Reflection preserves period-one membership. -/
theorem periodic_reflect {H : Set ℝ}
    (hH : ∀ x : ℝ, x + 1 ∈ H ↔ x ∈ H) :
    ∀ x : ℝ, x + 1 ∈ {y : ℝ | -y ∈ H} ↔ x ∈ {y : ℝ | -y ∈ H} := by
  intro x
  change -(x + 1) ∈ H ↔ -x ∈ H
  have heq : -(x + 1) + 1 = -x := by ring
  simpa only [heq] using (hH (-(x + 1))).symm

/-- The reflected version of the integer-dilation volume estimate. -/
theorem periodic_neg_dilate_unit_volume_le {H : Set ℝ}
    (hH : ∀ x : ℝ, x + 1 ∈ H ↔ x ∈ H) {n : ℕ} (hn : 0 < n) :
    volume ({x : ℝ | -((n : ℝ) * x) ∈ H} ∩ Icc (0 : ℝ) 1) ≤
      volume (H ∩ Icc (0 : ℝ) 1) := by
  exact (periodic_dilate_unit_volume_le (periodic_reflect hH) hn).trans_eq
    (periodic_reflect_unit_volume hH)

end Problem310Support

end

end OAI

-- ---- from OAI.MeasureTheory.DyadicAvoidance.GlobalFromPeriodic ----
namespace OAI

noncomputable section

open Set MeasureTheory

namespace Problem310Support

theorem signedDyadicUnion_open {H : ℕ → Set ℝ} (hH : ∀ j, IsOpen (H j)) :
    IsOpen (signedDyadicUnion H) := by
  apply isOpen_iUnion
  intro j
  exact ((hH j).preimage (continuous_const.mul continuous_id)).union
    ((hH j).preimage (continuous_const.mul continuous_id).neg)

/-- The cost of pairing and summing the dyadic pullbacks is at most
 twice the sum of the original period densities. -/
theorem signedDyadicUnion_volume_le {H : ℕ → Set ℝ}
    (hH : ∀ j, ∀ x : ℝ, x + 1 ∈ H j ↔ x ∈ H j) :
    volume (signedDyadicUnion H ∩ Icc (0 : ℝ) 1) ≤
      ∑' j : ℕ, 2 * volume (H j ∩ Icc (0 : ℝ) 1) := by
  rw [signedDyadicUnion, iUnion_inter]
  refine (measure_iUnion_le _).trans (ENNReal.tsum_le_tsum fun j => ?_)
  rw [union_inter_distrib_right, two_mul]
  refine (measure_union_le _ _).trans (add_le_add ?_ ?_)
  · simpa only [Nat.cast_pow, Nat.cast_ofNat] using
      periodic_dilate_unit_volume_le (hH j) (n := 2 ^ j) (by positivity)
  · simpa only [Nat.cast_pow, Nat.cast_ofNat] using
      periodic_neg_dilate_unit_volume_le (hH j) (n := 2 ^ j) (by positivity)

theorem dyadic_density_budget {η : ℝ} (hη : 0 ≤ η) :
    (∑' j : ℕ, (2 : ENNReal) *
      ENNReal.ofReal (6 * (η / 48 * ((2 : ℝ)⁻¹ ^ j)))) =
        ENNReal.ofReal (η / 2) := by
  have hterm (j : ℕ) : (2 : ENNReal) *
      ENNReal.ofReal (6 * (η / 48 * ((2 : ℝ)⁻¹ ^ j))) =
        ENNReal.ofReal (η / 4) * ((2 : ENNReal)⁻¹ ^ j) := by
    calc
      (2 : ENNReal) * ENNReal.ofReal (6 * (η / 48 * ((2 : ℝ)⁻¹ ^ j))) =
          ENNReal.ofReal (2 * (6 * (η / 48 * ((2 : ℝ)⁻¹ ^ j)))) := by
        rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
        norm_num
      _ = ENNReal.ofReal (η / 4 * ((2 : ℝ)⁻¹ ^ j)) := by
        congr 1
        ring
      _ = ENNReal.ofReal (η / 4) * ((2 : ENNReal)⁻¹ ^ j) := by
        rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (by positivity),
          ENNReal.ofReal_inv_of_pos (by norm_num : (0 : ℝ) < 2)]
        norm_num
  simp_rw [hterm]
  rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric_two]
  calc
    ENNReal.ofReal (η / 4) * 2 = ENNReal.ofReal ((η / 4) * 2) := by
      rw [ENNReal.ofReal_mul (by positivity)]
      norm_num
    _ = ENNReal.ofReal (η / 2) := by congr 1; ring

/-- The global compact avoidance theorem follows from the periodic hitting
lemma. All measure estimates, signed scales, and strict volume loss are
included in this implication. -/
theorem avoidance_of_periodic_hitting
    (hperiodic : ∀ p : ℝ, 0 < p → p < 1 → ∃ H : Set ℝ,
      IsOpen H ∧ (∀ x : ℝ, x + 1 ∈ H ↔ x ∈ H) ∧
      volume (H ∩ Icc (0 : ℝ) 1) ≤ ENNReal.ofReal (6 * p) ∧
      ∀ x t : ℝ, t ∈ Icc (1 : ℝ) 2 → ∃ n : ℕ, 1 ≤ n ∧
        x + t * ((2 : ℝ)⁻¹ ^ n) ∈ H) :
    ∀ η : ℝ, 0 < η → η < 1 → ∃ E : Set ℝ,
      E ⊆ Icc (0 : ℝ) 1 ∧ IsCompact E ∧
      volume E > ENNReal.ofReal (1 - η) ∧
      ∀ x s : ℝ, s ≠ 0 → ∃ n : ℕ, 1 ≤ n ∧
        x + s * ((2 : ℝ)⁻¹ ^ n) ∉ E := by
  intro η hη hη1
  let p : ℕ → ℝ := fun j => η / 48 * ((2 : ℝ)⁻¹ ^ j)
  have hp₀ (j : ℕ) : 0 < p j := by dsimp [p]; positivity
  have hp₁ (j : ℕ) : p j < 1 := by
    have hpow : (2 : ℝ)⁻¹ ^ j ≤ 1 :=
      pow_le_one₀ (by norm_num) (by norm_num)
    have hcoef : 0 ≤ η / 48 := by positivity
    have hp_le : p j ≤ η / 48 := by
      dsimp [p]
      exact mul_le_of_le_one_right hcoef hpow
    linarith
  choose H hOpen hPer hDensity hHit using fun j => hperiodic (p j) (hp₀ j) (hp₁ j)
  have hsmall : volume (signedDyadicUnion H ∩ Icc (0 : ℝ) 1) ≤
      ENNReal.ofReal (η / 2) := by
    refine (signedDyadicUnion_volume_le hPer).trans ?_
    calc
      (∑' j : ℕ, (2 : ENNReal) * volume (H j ∩ Icc (0 : ℝ) 1)) ≤
          ∑' j : ℕ, (2 : ENNReal) * ENNReal.ofReal (6 * p j) :=
        ENNReal.tsum_le_tsum fun j => mul_le_mul_right (hDensity j) 2
      _ = ENNReal.ofReal (η / 2) := dyadic_density_budget hη.le
  have hcompact := compact_complement_volume (signedDyadicUnion_open hOpen) hη hη1 hsmall
  refine ⟨Icc (0 : ℝ) 1 \ signedDyadicUnion H, sdiff_subset, hcompact.1, hcompact.2, ?_⟩
  intro x s hs
  obtain ⟨n, hn, hhit⟩ := signedDyadicUnion_hits hHit x s hs
  exact ⟨n, hn, fun hx => hx.2 hhit⟩

end Problem310Support

end

end OAI

-- ---- platform node ----
open OAI OAI.Problem310Support
open Set MeasureTheory


theorem solution : type_of% @_root_.OAI.Problem310Support.avoidance_of_periodic_hitting := @_root_.OAI.Problem310Support.avoidance_of_periodic_hitting
