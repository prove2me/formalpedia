-- Prove2me | solution 1 for OAI.GaussianPropeller.Scalar.RadiusData.fourth_cap
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T13:37:18.957111+00:00
-- url     : https://prove2.me/submissions/6b3f4d16-3b98-4304-bdb8-dc817de0b19b

-- Generated from openai/math@1581d4c lean/OAI/Probability/GaussianPropeller/Scalar.lean:L424-L468
-- (upload_full_project.md Phase 4): solution for node OAI.GaussianPropeller.Scalar.RadiusData.fourth_cap. The node keeps its source
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

theorem clipped_charge {A s q u δ : ℝ} (hd : 0 < A - 0.15) (hs : 0 < s)
    (hq : 0 ≤ q) (hqu : q ≤ u) (hds : (A - 0.15) * s = 0.415)
    (hδ0 : 0 ≤ δ) (hδ : charge A u ≤ δ) :
    (A - 0.15) * q / (s + q) * (s ^ 2 - u ^ 2) ≤ δ := by
  have hden : 0 < s + q := by positivity
  have hcoef : 0 ≤ (A - 0.15) * q / (s + q) := by positivity
  by_cases hu : s ≤ u
  · have hsq : s ^ 2 - u ^ 2 ≤ 0 := by nlinarith
    exact (mul_nonpos_of_nonneg_of_nonpos hcoef hsq).trans hδ0
  · have hu' : u ≤ s := le_of_lt (lt_of_not_ge hu)
    have hprod : 0 ≤ (A - 0.15) * s * ((s - u) * (u - q)) :=
      mul_nonneg (by positivity) (mul_nonneg (sub_nonneg.mpr hu') (sub_nonneg.mpr hqu))
    have hdiff : 0 ≤ charge A u -
        (A - 0.15) * q / (s + q) * (s ^ 2 - u ^ 2) := by
      have heq : (charge A u - (A - 0.15) * q / (s + q) * (s ^ 2 - u ^ 2)) *
          (s + q) = (A - 0.15) * s * ((s - u) * (u - q)) := by
        dsimp [charge]
        rw [← hds]
        field_simp
        ring
      exact nonneg_of_mul_nonneg_left (heq.symm ▸ hprod) hden
    linarith

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

theorem prefix_norm {p : ℕ} (hp : p ≤ m) :
    (∑ i ∈ Finset.range p, D.r i ^ 2) ≤ 1 := by
  simpa [D.norm] using sum_prefix_le (fun i => D.r i ^ 2) hp (fun i _ => sq_nonneg _)

theorem prefix_budget {p : ℕ} (hp : p ≤ m) :
    (∑ i ∈ Finset.range p, D.δ i) ≤ 1 - A := by
  simpa [D.budget] using sum_prefix_le D.δ hp D.nonneg

theorem tail_coarse_cap (hm : 5 ≤ m) {i : ℕ} (hi : i < m) (hi4 : 4 ≤ i) :
    D.r i ≤ 0.45 := by
  have hn := D.prefix_norm (by omega : 5 ≤ m)
  have hp := D.pos i hi
  have h0 := D.radius_le hi (by omega : 0 ≤ i)
  have h1 := D.radius_le hi (by omega : 1 ≤ i)
  have h2 := D.radius_le hi (by omega : 2 ≤ i)
  have h3 := D.radius_le hi (by omega : 3 ≤ i)
  have h4 := D.radius_le hi hi4
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add] at hn
  nlinarith

theorem prefix_block_budget {p q : ℕ} (hpq : p + q ≤ m) :
    (∑ i ∈ Finset.range p, D.δ i) +
      (∑ i ∈ Finset.range q, D.δ (p + i)) ≤ 1 - A := by
  rw [← Finset.sum_range_add]
  exact D.prefix_budget hpq

theorem prefix_block_norm {p q : ℕ} (hpq : p + q ≤ m) :
    (∑ i ∈ Finset.range p, D.r i ^ 2) +
      (∑ i ∈ Finset.range q, D.r (p + i) ^ 2) ≤ 1 := by
  rw [← Finset.sum_range_add]
  exact D.prefix_norm hpq

theorem tail_base_charge {k : ℕ} (R : Regime A k) (hm : 5 ≤ m)
    (ht : 0.066 < D.r (m - 1)) {i : ℕ} (hi : i < m) (hi4 : 4 ≤ i) :
    charge A 0.066 ≤ D.δ i := by
  have h := min_charge_le (by linarith [R.A_lower] : 0.15 ≤ A)
    (ht.le.trans (D.minimum_le hi)) (D.tail_coarse_cap hm hi hi4)
  rw [min_eq_left R.tail_end_charge] at h
  exact h.trans (D.lower i hi)

theorem fourth_cap {k : ℕ} (R : Regime A k) (hm : 5 ≤ m) (hkm : 3 + k ≤ m)
    (ht : 0.066 < D.r (m - 1)) : D.r 3 ≤ 0.42 := by
  by_contra! h4
  have hk : 2 ≤ k := R.k_lower
  have hd : 0 < A - 0.15 := by linarith [R.A_lower]
  have hs : 0 < threshold A := div_pos (by norm_num) hd
  have hds : (A - 0.15) * threshold A = 0.415 := by
    unfold threshold
    field_simp
  have hcoef : 0 ≤ clipCoeff A := by unfold clipCoeff; positivity
  have hfirst : ∀ i < 4,
      clipCoeff A * ((threshold A) ^ 2 - D.r i ^ 2) ≤ D.δ i := by
    intro i hi
    have hi' : i < m := by omega
    exact clipped_charge hd hs (by norm_num)
      (h4.le.trans (D.radius_le (by omega : 3 < m) (by omega)))
      hds (D.nonneg i hi') (D.lower i hi')
  have hf := Finset.sum_le_sum (fun i hi => hfirst i (Finset.mem_range.mp hi))
  rw [← Finset.mul_sum, Finset.sum_sub_distrib] at hf
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_ofNat] at hf
  have htailnorm : (k - 1 : ℕ) * (0.066 : ℝ) ^ 2 ≤
      ∑ i ∈ Finset.range (k - 1), D.r (4 + i) ^ 2 := by
    have hterm : ∀ i < k - 1, (0.066 : ℝ) ^ 2 ≤ D.r (4 + i) ^ 2 := by
      intro i hi
      have hi' : 4 + i < m := by omega
      have hr := ht.trans_le (D.minimum_le hi')
      nlinarith
    simpa using Finset.sum_le_sum (fun i hi => hterm i (Finset.mem_range.mp hi))
  have hn := D.prefix_block_norm (by omega : 4 + (k - 1) ≤ m)
  have hnm : (∑ i ∈ Finset.range 4, D.r i ^ 2) ≤
      1 - (k - 1 : ℕ) * (0.066 : ℝ) ^ 2 := by linarith
  have hf' := mul_le_mul_of_nonneg_left (sub_le_sub_left hnm (4 * (threshold A) ^ 2)) hcoef
  have htbudget : (k - 1 : ℕ) * charge A 0.066 ≤
      ∑ i ∈ Finset.range (k - 1), D.δ (4 + i) := by
    have hterm : ∀ i < k - 1, charge A 0.066 ≤ D.δ (4 + i) := by
      intro i hi
      exact D.tail_base_charge R hm ht (by omega) (by omega)
    simpa using Finset.sum_le_sum (fun i hi => hterm i (Finset.mem_range.mp hi))
  have hb := D.prefix_block_budget (by omega : 4 + (k - 1) ≤ m)
  have hcast : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ k)]
    norm_num
  rw [hcast] at hf' htbudget
  have hmarg := R.four_margin
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


theorem solution : type_of% @_root_.OAI.GaussianPropeller.Scalar.RadiusData.fourth_cap := @_root_.OAI.GaussianPropeller.Scalar.RadiusData.fourth_cap
