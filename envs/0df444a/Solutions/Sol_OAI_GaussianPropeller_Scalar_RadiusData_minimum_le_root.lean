-- Prove2me | solution 1 for OAI.GaussianPropeller.Scalar.RadiusData.minimum_le_root
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T13:43:34.724773+00:00
-- url     : https://prove2.me/submissions/6f5ae4ad-bbdb-42a6-a2ed-a7a879ee87a1

-- Generated from openai/math@1581d4c lean/OAI/Probability/GaussianPropeller/Scalar.lean:L493-L509
-- (upload_full_project.md Phase 4): solution for node OAI.GaussianPropeller.Scalar.RadiusData.minimum_le_root. The node keeps its source
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
import Theorems.Thm_OAI_GaussianPropeller_Scalar_RadiusData_fourth_cap
import Theorems.Thm_OAI_GaussianPropeller_Scalar_RadiusData_minimum_charge_bound

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

namespace RadiusData

variable {m : ℕ} {A : ℝ} (D : RadiusData m A)

theorem radius_le {i j : ℕ} (hj : j < m) (hij : i ≤ j) : D.r j ≤ D.r i :=
  D.ordered (show i ∈ Set.Iio m by exact lt_of_le_of_lt hij hj) hj hij

theorem tail_cap {k : ℕ} (R : Regime A k) (hm : 5 ≤ m) (hkm : 3 + k ≤ m)
    (ht : 0.066 < D.r (m - 1)) {i : ℕ} (hi : i < m) (hi3 : 3 ≤ i) :
    D.r i ≤ 0.42 :=
  (D.radius_le hi hi3).trans (D.fourth_cap R hm hkm ht)

theorem minimum_le_root {k : ℕ} (R : Regime A k) (hm : 5 ≤ m)
    (hkm : 3 + k ≤ m) (ht : 0.066 < D.r (m - 1)) :
    D.r (m - 1) ≤ smallRoot A k := by
  have hb := D.minimum_charge_bound R hm hkm ht
  have hcap := D.tail_cap R hm hkm ht (by omega : m - 1 < m) (by omega : 3 ≤ m - 1)
  have hd : 0 ≤ A - 0.15 := by linarith [R.A_lower]
  have hk : (0 : ℝ) < k := by exact_mod_cast (lt_of_lt_of_le (by omega : 0 < 2) R.k_lower)
  by_contra! h
  have hslope : 0 < 0.415 - (A - 0.15) * (D.r (m - 1) + smallRoot A k) := by
    have hmul := mul_le_mul_of_nonneg_left hcap hd
    linarith [R.root_slope]
  have hprod := mul_pos (sub_pos.mpr h) hslope
  have hcharge : charge A (smallRoot A k) < charge A (D.r (m - 1)) := by
    dsimp [charge]
    nlinarith
  have hmul := mul_lt_mul_of_pos_left hcharge hk
  linarith [R.root_eq]

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


theorem solution : type_of% @_root_.OAI.GaussianPropeller.Scalar.RadiusData.minimum_le_root := @_root_.OAI.GaussianPropeller.Scalar.RadiusData.minimum_le_root
