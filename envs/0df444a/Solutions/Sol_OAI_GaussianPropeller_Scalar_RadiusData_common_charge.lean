-- Prove2me | solution 1 for OAI.GaussianPropeller.Scalar.RadiusData.common_charge
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T13:35:29.892923+00:00
-- url     : https://prove2.me/submissions/7cf841c1-8e0f-4683-bf58-8360dfe87d6a

-- Generated from openai/math@1581d4c lean/OAI/Probability/GaussianPropeller/Scalar.lean:L338-L370
-- (upload_full_project.md Phase 4): solution for node OAI.GaussianPropeller.Scalar.RadiusData.common_charge. The node keeps its source
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

-- ---- from OAI.Probability.GaussianPropeller.Scalar ----
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

namespace GaussianPropeller
namespace Scalar

theorem sum_split (f : ℕ → ℝ) {p m : ℕ} (hp : p ≤ m) :
    (∑ i ∈ Finset.range p, f i) + (∑ i ∈ Finset.range (m - p), f (p + i)) =
      ∑ i ∈ Finset.range m, f i := by
  rw [← Finset.sum_range_add, Nat.add_sub_of_le hp]

namespace RadiusData

variable {m : ℕ} {A : ℝ} (D : RadiusData m A)

theorem radius_le {i j : ℕ} (hj : j < m) (hij : i ≤ j) : D.r j ≤ D.r i :=
  D.ordered (show i ∈ Set.Iio m by exact lt_of_le_of_lt hij hj) hj hij

theorem common_charge (hm : 3 ≤ m) (hA : 0.884 ≤ A) :
    (1 - (D.r 0 ^ 2 + D.r 1 ^ 2)) * (0.415 / D.r 2 - 0.734) ≤ 0.116 := by
  let u := D.r 2
  have hu : 0 < u := D.pos 2 (by omega)
  have hterm : ∀ i < m - 2,
      D.r (2 + i) ^ 2 * (0.415 / u - (A - 0.15)) ≤ D.δ (2 + i) := by
    intro i hi
    have hi' : 2 + i < m := by omega
    have hri := D.pos (2 + i) hi'
    have hle : D.r (2 + i) ≤ u := D.radius_le hi' (by omega)
    have hmul : D.r (2 + i) ^ 2 * (0.415 / u) ≤ 0.415 * D.r (2 + i) := by
      rw [← mul_div_assoc]
      apply (div_le_iff₀ hu).mpr
      nlinarith [mul_nonneg (le_of_lt hri) (sub_nonneg.mpr hle)]
    have hlower := D.lower (2 + i) hi'
    dsimp [charge] at hlower
    nlinarith
  have hsum := Finset.sum_le_sum (fun i hi => hterm i (Finset.mem_range.mp hi))
  rw [← Finset.sum_mul] at hsum
  have hn := sum_split (fun i => D.r i ^ 2) (by omega : 2 ≤ m)
  have hb := sum_split D.δ (by omega : 2 ≤ m)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add] at hn hb
  rw [D.norm] at hn
  rw [D.budget] at hb
  have hd0 := D.nonneg 0 (by omega)
  have hd1 := D.nonneg 1 (by omega)
  have hL : 0 ≤ D.r 0 ^ 2 + D.r 1 ^ 2 := by positivity
  have hAdj : 0 ≤ (A - 0.884) * (D.r 0 ^ 2 + D.r 1 ^ 2) := by positivity
  have hns : (∑ i ∈ Finset.range (m - 2), D.r (2 + i) ^ 2) =
      1 - (D.r 0 ^ 2 + D.r 1 ^ 2) := by linarith
  rw [hns] at hsum
  dsimp [u] at hsum
  nlinarith

end RadiusData

end Scalar

end GaussianPropeller

end OAI

-- ---- platform node ----
open OAI OAI.GaussianPropeller OAI.GaussianPropeller.Scalar OAI.GaussianPropeller.Scalar.RadiusData
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


theorem solution : type_of% @_root_.OAI.GaussianPropeller.Scalar.RadiusData.common_charge := @_root_.OAI.GaussianPropeller.Scalar.RadiusData.common_charge
