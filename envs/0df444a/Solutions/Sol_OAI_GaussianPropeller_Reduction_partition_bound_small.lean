-- Prove2me | solution 1 for OAI.GaussianPropeller.Reduction.partition_bound_small
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T14:27:01.552989+00:00
-- url     : https://prove2.me/submissions/a93e0dc3-7788-4802-bd60-a475de268019

-- Generated from openai/math@1581d4c lean/OAI/Probability/GaussianPropeller/Elimination.lean:L118-L134
-- (upload_full_project.md Phase 4): solution for node OAI.GaussianPropeller.Reduction.partition_bound_small. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_GaussianPropeller
import Definitions.Def_OAI_Probability_GaussianPropeller_Moments
import Definitions.Def_OAI_Probability_GaussianPropeller_Dual
import Definitions.Def_OAI_Probability_GaussianPropeller_Deletion
import Definitions.Def_OAI_Probability_GaussianPropeller_Translation
import Definitions.Def_OAI_Probability_GaussianPropeller_HeatConvolution
import Definitions.Def_OAI_Probability_GaussianPropeller_Quantile
import Definitions.Def_OAI_Probability_GaussianPropeller_QuantileCalculus
import Definitions.Def_OAI_Probability_GaussianPropeller_HeatMaximum
import Definitions.Def_OAI_Probability_GaussianPropeller_SmoothedConcavity
import Definitions.Def_OAI_Probability_GaussianPropeller_SoftMinimum
import Definitions.Def_OAI_Probability_GaussianPropeller_ConeConcavity
import Definitions.Def_OAI_Probability_GaussianPropeller_OneCell
import Definitions.Def_OAI_Probability_GaussianPropeller_Mills
import Definitions.Def_OAI_Probability_GaussianPropeller_Taylor
import Definitions.Def_OAI_Probability_GaussianPropeller_ProbabilityBounds
import Definitions.Def_OAI_Probability_GaussianPropeller_Attainment
import Definitions.Def_OAI_Probability_GaussianPropeller_PairIntegral
import Definitions.Def_OAI_Probability_GaussianPropeller_ResidualBounds
import Definitions.Def_OAI_Probability_GaussianPropeller_Polar
import Definitions.Def_OAI_Probability_GaussianPropeller_CapIntegral
import Definitions.Def_OAI_Probability_GaussianPropeller_Coordinates
import Definitions.Def_OAI_Probability_GaussianPropeller_CapBounds
import Definitions.Def_OAI_Probability_GaussianPropeller_CapNumeric
import Definitions.Def_OAI_Probability_GaussianPropeller_Geometry
import Definitions.Def_OAI_Probability_GaussianPropeller_QuarticCertificates
import Definitions.Def_OAI_Probability_GaussianPropeller_CapCertificates
import Definitions.Def_OAI_Probability_GaussianPropeller_Scalar
import Definitions.Def_OAI_Probability_GaussianPropeller_Configuration
import Theorems.Thm_OAI_GaussianPropeller_Reduction_append_empty_partition
import Theorems.Thm_OAI_GaussianPropeller_Reduction_pairing_le_width
import Theorems.Thm_OAI_GaussianPropeller_Reduction_width_three

-- ---- from OAI.Probability.GaussianPropeller.Moments ----
namespace OAI

universe uF

open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace GaussianPropeller

open scoped RealInnerProductSpace

theorem value_nonneg {d k : ℕ} (A : Fin k → Set (Space d)) : 0 ≤ value A := by
  exact Finset.sum_nonneg (fun i _ => sq_nonneg ‖centroid (A i)‖)

end GaussianPropeller

end OAI

-- ---- from OAI.Probability.GaussianPropeller.Dual ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace GaussianPropeller
open scoped RealInnerProductSpace

namespace Reduction

variable {d k : ℕ} [NeZero k]

omit [NeZero k] in
theorem norm_moments_sq (A : Fin k → Set (Space d)) : ‖moments A‖ ^ 2 = value A :=
  PiLp.norm_sq_eq_of_L2 _ _

end Reduction

end GaussianPropeller

end OAI

-- ---- from OAI.Probability.GaussianPropeller.Attainment ----
namespace OAI

universe uE

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open scoped RealInnerProductSpace
open scoped RealInnerProductSpace
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal RealInnerProductSpace
open Filter
open scoped Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
open scoped RealInnerProductSpace
open Set Filter
open scoped Topology RealInnerProductSpace
open scoped NNReal
open Set Filter
open scoped Topology RealInnerProductSpace NNReal
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology RealInnerProductSpace
open MeasureTheory Set Filter
open scoped Topology BigOperators
open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace Topology

namespace GaussianPropeller.Reduction

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace

theorem perimeter_sq_le {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (a b c : E) : (‖a-b‖ + ‖a-c‖ + ‖b-c‖)^2 ≤
      9 * (‖a‖^2 + ‖b‖^2 + ‖c‖^2) := by
  have hcs : (‖a-b‖ + ‖a-c‖ + ‖b-c‖)^2 ≤
      3 * (‖a-b‖^2 + ‖a-c‖^2 + ‖b-c‖^2) := by
    nlinarith [sq_nonneg (‖a-b‖ - ‖a-c‖), sq_nonneg (‖a-b‖ - ‖b-c‖),
      sq_nonneg (‖a-c‖ - ‖b-c‖)]
  have hid : ‖a-b‖^2 + ‖a-c‖^2 + ‖b-c‖^2 =
      3 * (‖a‖^2 + ‖b‖^2 + ‖c‖^2) - ‖a+b+c‖^2 := by
    simp only [norm_sub_sq_real, norm_add_sq_real, inner_add_left]
    ring
  rw [hid] at hcs
  nlinarith [sq_nonneg ‖a+b+c‖]

theorem width_three_sq_le {d : ℕ} (v : Tuple d 3) :
    (width v)^2 ≤ (9 / (8 * Real.pi)) * ‖v‖^2 := by
  have hp := perimeter_sq_le (v.ofLp 0) (v.ofLp 1) (v.ofLp 2)
  have hnorm : ‖v‖^2 = ‖v.ofLp 0‖^2 + ‖v.ofLp 1‖^2 + ‖v.ofLp 2‖^2 := by
    simp only [PiLp.norm_sq_eq_of_L2, Fin.sum_univ_three]
  rw [← hnorm] at hp
  rw [width_three, div_pow]
  have hs : (2 * Real.sqrt (2 * Real.pi))^2 = 8 * Real.pi := by
    rw [mul_pow, Real.sq_sqrt (by positivity)]
    ring
  rw [hs]
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < 8 * Real.pi)).mpr
  calc
    _ ≤ 9 * ‖v‖^2 := hp
    _ = 9 / (8 * Real.pi) * ‖v‖^2 * (8 * Real.pi) := by
      field_simp

theorem three_partition_bound {d : ℕ} {A : Fin 3 → Set (Space d)} (hA : IsPartition A) :
    value A ≤ 9 / (8 * Real.pi) := by
  have hpair : value A ≤ width (moments A) := by
    simpa only [real_inner_self_eq_norm_sq, norm_moments_sq] using
      pairing_le_width hA (moments A)
  have hsq := width_three_sq_le (moments A)
  rw [norm_moments_sq] at hsq
  have hn := value_nonneg A
  have hw : 0 ≤ width (moments A) := hn.trans hpair
  have hval := (sq_le_sq₀ hn hw).mpr hpair
  have hB : (0 : ℝ) < 9 / (8 * Real.pi) := by positivity
  nlinarith

theorem append_empty_value {d k : ℕ} (A : Fin k → Set (Space d)) :
    value (Fin.lastCases ∅ A) = value A := by
  simp [value, Fin.sum_univ_castSucc]

end GaussianPropeller.Reduction

namespace GaussianPropeller

end GaussianPropeller

end OAI

-- ---- from OAI.Probability.GaussianPropeller.Elimination ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open scoped RealInnerProductSpace
open scoped RealInnerProductSpace
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal RealInnerProductSpace
open Filter
open scoped Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
open scoped RealInnerProductSpace
open Set Filter
open scoped Topology RealInnerProductSpace
open scoped NNReal
open Set Filter
open scoped Topology RealInnerProductSpace NNReal
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology RealInnerProductSpace
open MeasureTheory Set Filter
open scoped Topology BigOperators
open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace Topology ENNReal
open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace Topology ENNReal
open Metric
open MeasureTheory ProbabilityTheory Set
open scoped RealInnerProductSpace ENNReal
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal RealInnerProductSpace

namespace GaussianPropeller.Reduction.Configuration
variable {d k:ℕ}

end GaussianPropeller.Reduction.Configuration

namespace GaussianPropeller.Reduction
variable {d k:ℕ}

lemma partition_bound_small {A:Fin k→Set (Space d)} (hk:k≤3) (hA:IsPartition A) :
    value A≤9/(8*Real.pi) := by
  have he:∃ B:Fin 3→Set (Space d), IsPartition B ∧ value B=value A := by
    have hc:∀ m, k ≤ m → ∃ B:Fin m→Set (Space d), IsPartition B ∧ value B=value A := by
      intro m hm
      induction m,hm using Nat.le_induction with
      | base => exact ⟨A,hA,rfl⟩
      | succ m hm ih =>
        obtain ⟨B,hB,hv⟩:=ih
        let B' : Fin (m+1) → Set (Space d) := Fin.lastCases ∅ B
        have hp : IsPartition B' := append_empty_partition (A := B) hB
        have he : value B' = value B := append_empty_value B
        exact ⟨B',hp,he.trans hv⟩
    exact hc 3 hk
  obtain ⟨B,hB,hv⟩:=he
  rw [←hv]
  exact three_partition_bound hB

end GaussianPropeller.Reduction

end OAI

-- ---- platform node ----
open OAI OAI.GaussianPropeller OAI.GaussianPropeller.Reduction
open MeasureTheory ProbabilityTheory
open scoped ENNReal
open scoped RealInnerProductSpace
open scoped RealInnerProductSpace
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal RealInnerProductSpace
open Filter
open scoped Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
open scoped RealInnerProductSpace
open Set Filter
open scoped Topology RealInnerProductSpace
open scoped NNReal
open Set Filter
open scoped Topology RealInnerProductSpace NNReal
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology RealInnerProductSpace
open MeasureTheory Set Filter
open scoped Topology BigOperators
open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace Topology ENNReal
open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace Topology ENNReal
open Metric
open MeasureTheory ProbabilityTheory Set
open scoped RealInnerProductSpace ENNReal
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal RealInnerProductSpace


theorem solution : type_of% @_root_.OAI.GaussianPropeller.Reduction.partition_bound_small := @_root_.OAI.GaussianPropeller.Reduction.partition_bound_small
