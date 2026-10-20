-- Prove2me | solution 1 for OAI.GaussianPropeller.Scalar.RadiusData.third_large
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T13:48:39.182478+00:00
-- url     : https://prove2.me/submissions/b66c7c36-5c31-4c35-87ca-38b8372b91d8

-- Generated from openai/math@1581d4c lean/OAI/Probability/GaussianPropeller/Scalar.lean:L524-L589
-- (upload_full_project.md Phase 4): solution for node OAI.GaussianPropeller.Scalar.RadiusData.third_large. The node keeps its source
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
import Theorems.Thm_OAI_GaussianPropeller_Scalar_RadiusData_common_charge
import Theorems.Thm_OAI_GaussianPropeller_Scalar_RadiusData_fourth_cap
import Theorems.Thm_OAI_GaussianPropeller_Scalar_RadiusData_minimum_charge_bound
import Theorems.Thm_OAI_GaussianPropeller_Scalar_RadiusData_minimum_le_root

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

theorem third_radius_gt {L u : ℝ} (hu : 0 < u) (hL : L ≤ 8 / 9)
    (hcharge : (1 - L) * (0.415 / u - 0.734) ≤ 0.116) : 0.23 < u := by
  by_contra! h
  have hd : (0.415 : ℝ) / 0.23 ≤ 0.415 / u :=
    div_le_div_of_nonneg_left (by norm_num) hu h
  have hm := mul_le_mul_of_nonneg_left (sub_le_sub_right hd 0.734)
    (show 0 ≤ 1 - L by linarith)
  norm_num at hm
  nlinarith

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

theorem finalBudget_concave {A k : ℝ} (hA : 0.15 ≤ A) (hk : 0 ≤ k) :
    ConcaveOn ℝ (Set.Ici 0) (finalBudget A k) := by
  have hsqrt : ConcaveOn ℝ (Set.Ici 0) (fun t : ℝ =>
      (0.415 * Real.sqrt 2.6) * Real.sqrt t) :=
    Real.strictConcaveOn_sqrt.concaveOn.smul (by positivity)
  have hlin : ConvexOn ℝ (Set.Ici 0) (fun t : ℝ => (2.6 * (A - 0.15)) * t) :=
    (convexOn_id (convex_Ici (0 : ℝ))).smul (by positivity)
  have hquad := ((charge_concave hA).subset (Set.subset_univ _) (convex_Ici 0)).smul hk
  have heq : Set.EqOn
      (fun t : ℝ => (0.415 * Real.sqrt 2.6) * Real.sqrt t -
        (2.6 * (A - 0.15)) * t + k * charge A t)
      (finalBudget A k) (Set.Ici 0) := by
    intro t ht
    have ht0 : 0 ≤ t := ht
    have hsq := Real.sq_sqrt (show 0 ≤ 2.6 * t by positivity)
    dsimp [finalBudget, charge]
    rw [hsq, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2.6)]
    ring
  exact ((hsqrt.sub hlin).add hquad).congr heq

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

theorem first_two_cap (hm : 2 ≤ m) : D.r 0 ^ 2 + D.r 1 ^ 2 ≤ 8 / 9 := by
  have h0 := D.cap 0 (by omega)
  have h1 := D.cap 1 (by omega)
  have hp0 := D.pos 0 (by omega)
  have hp1 := D.pos 1 (by omega)
  nlinarith

theorem prefix_block_budget {p q : ℕ} (hpq : p + q ≤ m) :
    (∑ i ∈ Finset.range p, D.δ i) +
      (∑ i ∈ Finset.range q, D.δ (p + i)) ≤ 1 - A := by
  rw [← Finset.sum_range_add]
  exact D.prefix_budget hpq

theorem tail_cap {k : ℕ} (R : Regime A k) (hm : 5 ≤ m) (hkm : 3 + k ≤ m)
    (ht : 0.066 < D.r (m - 1)) {i : ℕ} (hi : i < m) (hi3 : 3 ≤ i) :
    D.r i ≤ 0.42 :=
  (D.radius_le hi hi3).trans (D.fourth_cap R hm hkm ht)

theorem tail_charge {k : ℕ} (R : Regime A k) (hm : 5 ≤ m) (hkm : 3 + k ≤ m)
    (ht : 0.066 < D.r (m - 1)) {i : ℕ} (hi : i < m) (hi3 : 3 ≤ i) :
    charge A (D.r (m - 1)) ≤ D.δ i := by
  have hbudget := D.minimum_charge_bound R hm hkm ht
  have hk : (0 : ℝ) < k := by exact_mod_cast (lt_of_lt_of_le (by omega : 0 < 2) R.k_lower)
  have hcharge : charge A (D.r (m - 1)) ≤ charge A 0.42 := by
    have h := (lt_of_le_of_lt hbudget R.cap_charge)
    nlinarith
  have h := min_charge_le (by linarith [R.A_lower] : 0.15 ≤ A)
    (D.minimum_le hi) (D.tail_cap R hm hkm ht hi hi3)
  rw [min_eq_left hcharge] at h
  exact h.trans (D.lower i hi)

theorem third_large {k : ℕ} (R : Regime A k) (hm : 5 ≤ m) (hkm : 3 + k ≤ m)
    (ht : 0.066 < D.r (m - 1)) : 2.6 * D.r (m - 1) < D.r 2 ^ 2 := by
  let t := D.r (m - 1)
  let t₀ := smallRoot A k
  have ht0 : 0 < t := by dsimp [t]; linarith
  have htroot : t ≤ t₀ := D.minimum_le_root R hm hkm ht
  have htrootpos : 0 < t₀ := by dsimp [t₀]; linarith [R.root_lower]
  have hd : 0 < A - 0.15 := by linarith [R.A_lower]
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have htlt : t₀ < 0.12 := R.root_upper
  have he_inc : charge A 0.066 ≤ charge A t := by
    have hmul := mul_le_mul_of_nonneg_left (show 0.066 + t ≤ 0.42 + t₀ by linarith) hd.le
    have hslope : 0 ≤ 0.415 - (A - 0.15) * (t + 0.066) := by
      linarith [R.root_slope]
    have hprod := mul_nonneg (show 0 ≤ t - 0.066 by dsimp [t]; linarith) hslope
    dsimp [charge]
    nlinarith
  have hfst : 1 - A < charge A 0.23 + (k : ℝ) * charge A t := by
    have hm := mul_le_mul_of_nonneg_left he_inc hk
    linarith [R.third_margin]
  have hspos : 0 < threshold A := div_pos (by norm_num) hd
  have hslopeeq : (A - 0.15) * threshold A = 0.415 := by
    unfold threshold
    field_simp
  have hsqrtpos : 0 < Real.sqrt (2.6 * t₀) := Real.sqrt_pos.mpr (by positivity)
  have hsqrtsq := Real.sq_sqrt (show 0 ≤ 2.6 * t₀ by positivity)
  have hsqrtlt : Real.sqrt (2.6 * t₀) < threshold A := by
    have hcap := R.root_cap
    dsimp [t₀] at hsqrtsq ⊢
    nlinarith
  have hepos : 0 < charge A (Real.sqrt (2.6 * t₀)) := by
    have hp := mul_pos hd (sub_pos.mpr hsqrtlt)
    have hp' := mul_pos hsqrtpos hp
    dsimp [charge]
    nlinarith
  have hend : 1 - A < finalBudget A k t₀ := by
    dsimp [finalBudget]
    linarith [R.root_eq]
  have hlower := (finalBudget_concave (by linarith [R.A_lower] : 0.15 ≤ A) hk).min_le_of_mem_Icc (by norm_num : (0.066 : ℝ) ∈ Set.Ici 0)
      (show t₀ ∈ Set.Ici 0 by exact htrootpos.le) (show t ∈ Set.Icc 0.066 t₀ by exact ⟨ht.le, htroot⟩)
  have hsnd : 1 - A < finalBudget A k t :=
    lt_of_lt_of_le (lt_min R.final_margin hend) hlower
  by_contra! hthird
  have hthirdpos := D.pos 2 (by omega)
  have hthirdlow := third_radius_gt hthirdpos (D.first_two_cap (by omega))
    (D.common_charge (by omega) R.A_lower)
  have hsqrt := Real.sq_sqrt (show 0 ≤ 2.6 * t by positivity)
  have hthirdhi : D.r 2 ≤ Real.sqrt (2.6 * t) := by
    nlinarith [Real.sqrt_nonneg (2.6 * t)]
  have hthirdcharge := (min_charge_le (by linarith [R.A_lower] : 0.15 ≤ A)
    hthirdlow.le hthirdhi).trans (D.lower 2 (by omega))
  have htailterm : ∀ i < k, charge A t ≤ D.δ (3 + i) := by
    intro i hi
    exact D.tail_charge R hm hkm ht (by omega) (by omega)
  have htail := Finset.sum_le_sum (fun i hi => htailterm i (Finset.mem_range.mp hi))
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at htail
  have hb := D.prefix_block_budget hkm
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add] at hb
  have h0 := D.nonneg 0 (by omega)
  have h1 := D.nonneg 1 (by omega)
  dsimp [finalBudget] at hsnd
  rcases le_total (charge A 0.23) (charge A (Real.sqrt (2.6 * t))) with h | h
  · rw [min_eq_left h] at hthirdcharge
    linarith
  · rw [min_eq_right h] at hthirdcharge
    linarith

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


theorem solution : type_of% @_root_.OAI.GaussianPropeller.Scalar.RadiusData.third_large := @_root_.OAI.GaussianPropeller.Scalar.RadiusData.third_large
