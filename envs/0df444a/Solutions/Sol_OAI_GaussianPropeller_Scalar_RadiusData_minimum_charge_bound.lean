-- Prove2me | solution 1 for OAI.GaussianPropeller.Scalar.RadiusData.minimum_charge_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T13:41:41.417987+00:00
-- url     : https://prove2.me/submissions/002f0b7d-e018-4b1a-aa6a-dac139bf24f4

-- Generated from openai/math@1581d4c lean/OAI/Probability/GaussianPropeller/Scalar.lean:L475-L491
-- (upload_full_project.md Phase 4): solution for node OAI.GaussianPropeller.Scalar.RadiusData.minimum_charge_bound. The node keeps its source
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

theorem charge_concave {A : ℝ} (hA : 0.15 ≤ A) :
    ConcaveOn ℝ Set.univ (charge A) := by
  have hlin : ConcaveOn ℝ (Set.univ : Set ℝ) (fun u : ℝ => (0.415 : ℝ) * u) :=
    (concaveOn_id convex_univ).smul (by norm_num)
  have hquad : ConvexOn ℝ (Set.univ : Set ℝ) (fun u : ℝ => (A - 0.15) * u ^ 2) :=
    (Even.convexOn_pow (by decide : Even (2 : ℕ))).smul (by linarith)
  exact hlin.sub hquad

theorem min_charge_le {A a b u : ℝ} (hA : 0.15 ≤ A)
    (ha : a ≤ u) (hb : u ≤ b) : min (charge A a) (charge A b) ≤ charge A u :=
  (charge_concave hA).min_le_of_mem_Icc (Set.mem_univ _) (Set.mem_univ _) ⟨ha, hb⟩

theorem sum_split (f : ℕ → ℝ) {p m : ℕ} (hp : p ≤ m) :
    (∑ i ∈ Finset.range p, f i) + (∑ i ∈ Finset.range (m - p), f (p + i)) =
      ∑ i ∈ Finset.range m, f i := by
  rw [← Finset.sum_range_add, Nat.add_sub_of_le hp]

theorem sum_prefix_le (f : ℕ → ℝ) {p m : ℕ} (hp : p ≤ m)
    (hf : ∀ i < m, 0 ≤ f i) :
    (∑ i ∈ Finset.range p, f i) ≤ ∑ i ∈ Finset.range m, f i := by
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hp)
    (fun i hi _ => hf i (Finset.mem_range.mp hi))

namespace RadiusData

variable {m : ℕ} {A : ℝ} (D : RadiusData m A)

theorem radius_le {i j : ℕ} (hj : j < m) (hij : i ≤ j) : D.r j ≤ D.r i :=
  D.ordered (show i ∈ Set.Iio m by exact lt_of_le_of_lt hij hj) hj hij

theorem minimum_le {i : ℕ} (hi : i < m) : D.r (m - 1) ≤ D.r i :=
  D.radius_le (by omega) (by omega)

theorem prefix_budget {p : ℕ} (hp : p ≤ m) :
    (∑ i ∈ Finset.range p, D.δ i) ≤ 1 - A := by
  simpa [D.budget] using sum_prefix_le D.δ hp D.nonneg

theorem block_budget {p q : ℕ} (hpq : p + q ≤ m) :
    ∑ i ∈ Finset.range q, D.δ (p + i) ≤ 1 - A := by
  have h := D.prefix_budget hpq
  have hs := sum_split D.δ (by omega : p ≤ p + q)
  rw [Nat.add_sub_cancel_left] at hs
  have hn : 0 ≤ ∑ i ∈ Finset.range p, D.δ i :=
    Finset.sum_nonneg (fun i hi => D.nonneg i (by have := Finset.mem_range.mp hi; omega))
  linarith

theorem tail_cap {k : ℕ} (R : Regime A k) (hm : 5 ≤ m) (hkm : 3 + k ≤ m)
    (ht : 0.066 < D.r (m - 1)) {i : ℕ} (hi : i < m) (hi3 : 3 ≤ i) :
    D.r i ≤ 0.42 :=
  (D.radius_le hi hi3).trans (D.fourth_cap R hm hkm ht)

theorem minimum_charge_bound {k : ℕ} (R : Regime A k) (hm : 5 ≤ m)
    (hkm : 3 + k ≤ m) (ht : 0.066 < D.r (m - 1)) :
    (k : ℝ) * charge A (D.r (m - 1)) ≤ 1 - A := by
  have hterm : ∀ i < k,
      min (charge A (D.r (m - 1))) (charge A 0.42) ≤ D.δ (3 + i) := by
    intro i hi
    have hi' : 3 + i < m := by omega
    exact (min_charge_le (by linarith [R.A_lower] : 0.15 ≤ A)
      (D.minimum_le hi') (D.tail_cap R hm hkm ht hi' (by omega))).trans (D.lower _ hi')
  have hs := Finset.sum_le_sum (fun i hi => hterm i (Finset.mem_range.mp hi))
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hs
  have hb := D.block_budget hkm
  by_cases h : charge A (D.r (m - 1)) ≤ charge A 0.42
  · rw [min_eq_left h] at hs
    exact hs.trans hb
  · rw [min_eq_right (le_of_not_ge h)] at hs
    linarith [R.cap_charge]

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


theorem solution : type_of% @_root_.OAI.GaussianPropeller.Scalar.RadiusData.minimum_charge_bound := @_root_.OAI.GaussianPropeller.Scalar.RadiusData.minimum_charge_bound
