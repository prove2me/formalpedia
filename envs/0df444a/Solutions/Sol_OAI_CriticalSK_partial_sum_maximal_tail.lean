-- Prove2me | solution 1 for OAI.CriticalSK.partial_sum_maximal_tail
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-18T21:35:36.223631+00:00
-- url     : https://prove2.me/submissions/f823e6b6-5677-4ae6-8691-83d6862551d6

import Mathlib

section
-- module Solutions.OAIQW_CriticalSK.GaussianConcentration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators Topology NNReal ENNReal

open scoped BigOperators ENNReal NNReal Real Topology
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal
open scoped BigOperators NNReal
open scoped BigOperators
open scoped BigOperators InnerProductSpace
open Module
open Matrix Polynomial
open scoped BigOperators Topology
open Filter
open scoped BigOperators NNReal ENNReal Topology Pointwise Matrix.Norms.Elementwise
open Set Metric MeasureTheory MeasureTheory.Measure
open scoped ENNReal NNReal BigOperators
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Topology
open MeasureTheory MeasureTheory.Measure Set Metric
open scoped NNReal ENNReal BigOperators
open scoped NNReal ENNReal
open ProbabilityTheory
open Metric Set MeasureTheory
open scoped ENNReal Pointwise
open MeasureTheory Filter Set Real
open Finset Real
open scoped BigOperators ENNReal Topology
open Set MeasureTheory
open scoped BigOperators ENNReal
open MeasureTheory
open Finset Real Filter
open scoped Topology
namespace CriticalSK

section

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

lemma independent_product_submartingale {Y : ℕ → Ω → ℝ}
    (hY : ∀ i, StronglyMeasurable (Y i)) (hind : iIndepFun Y μ)
    (hint : ∀ n, Integrable (fun ω => ∏ i ∈ Finset.range (n + 1), Y i ω) μ)
    (hi : ∀ i, Integrable (Y i) μ) (hpos : ∀ i ω, 0 ≤ Y i ω)
    (hmean : ∀ i, 1 ≤ ∫ ω, Y i ω ∂μ) :
    Submartingale (fun n ω => ∏ i ∈ Finset.range (n + 1), Y i ω)
      (Filtration.natural Y hY) μ := by
  have hadp : StronglyAdapted (Filtration.natural Y hY)
      (fun n ω => ∏ i ∈ Finset.range (n + 1), Y i ω) := by
    intro n
    have hh : ∀ i ∈ Finset.range (n + 1),
        StronglyMeasurable[Filtration.natural Y hY n] (Y i) := by
      intro i hi
      exact (Filtration.stronglyAdapted_natural hY i).mono
        ((Filtration.natural Y hY).mono (Nat.le_of_lt_succ (Finset.mem_range.mp hi)))
    convert Finset.stronglyMeasurable_prod (Finset.range (n + 1)) hh using 1
    ext ω
    simp only [Finset.prod_apply]
  apply submartingale_nat hadp hint
  intro n
  have hid : (fun ω => ∏ i ∈ Finset.range (n + 1 + 1), Y i ω) =
      (fun ω => ∏ i ∈ Finset.range (n + 1), Y i ω) * Y (n + 1) := by
    funext ω
    simp [Finset.prod_range_succ]
  rw [hid]
  have hcond := condExp_mul_of_stronglyMeasurable_left (hadp n)
    (hid ▸ hint (n + 1)) (hi (n + 1))
  have hindcond := hind.condExp_natural_ae_eq_of_lt hY (Nat.lt_succ_self n)
  filter_upwards [hcond, hindcond] with ω hc he
  rw [hc]
  simp only [Pi.mul_apply]
  rw [he]
  exact le_mul_of_one_le_right
    (Finset.prod_nonneg (fun i _ => hpos i ω)) (hmean (n + 1))

lemma exp_partial_sum_submartingale {X : ℕ → Ω → ℝ} {c : ℝ≥0}
    (hX : ∀ i, StronglyMeasurable (X i)) (hind : iIndepFun X μ)
    (hmgf : ∀ i, HasSubgaussianMGF (X i) c μ)
    (hmean : ∀ i, ∫ ω, X i ω ∂μ = 0) (t : ℝ) :
    ∃ (F : Filtration ℕ ‹MeasurableSpace Ω›),
      Submartingale (fun n ω => Real.exp (t * ∑ i ∈ Finset.range (n + 1), X i ω)) F μ := by
  let Y : ℕ → Ω → ℝ := fun i ω => Real.exp (t * X i ω)
  have hY : ∀ i, StronglyMeasurable (Y i) := fun i =>
    Real.continuous_exp.comp_stronglyMeasurable ((hX i).const_mul t)
  have hYi : ∀ i, Integrable (Y i) μ := fun i => (hmgf i).integrable_exp_mul t
  have hindY : iIndepFun Y μ := hind.comp (fun _ x => Real.exp (t * x))
    (fun _ => Real.measurable_exp.comp (measurable_const.mul measurable_id))
  have heq (n : ℕ) : (fun ω => ∏ i ∈ Finset.range (n + 1), Y i ω) =
      (fun ω => Real.exp (t * ∑ i ∈ Finset.range (n + 1), X i ω)) := by
    funext ω
    simp only [Y, Finset.mul_sum, Real.exp_sum]
  have hint (n : ℕ) : Integrable (fun ω => ∏ i ∈ Finset.range (n + 1), Y i ω) μ := by
    rw [heq]
    exact (HasSubgaussianMGF.sum_of_iIndepFun hind (fun i _ => hmgf i)).integrable_exp_mul t
  have hm (i : ℕ) : 1 ≤ ∫ ω, Y i ω ∂μ := by
    have h := integral_mono (((hmgf i).integrable.const_mul t).add (integrable_const 1))
      (hYi i) (fun ω => Real.add_one_le_exp (t * X i ω))
    change (∫ ω, t * X i ω + 1 ∂μ) ≤ ∫ ω, Y i ω ∂μ at h
    rw [integral_add ((hmgf i).integrable.const_mul t) (integrable_const 1),
      integral_const_mul, hmean i] at h
    simpa using h
  refine ⟨Filtration.natural Y hY, ?_⟩
  have h := independent_product_submartingale hY hindY hint hYi
    (fun i ω => (Real.exp_pos _).le) hm
  convert h using 1
  funext n
  exact (heq n).symm

lemma partial_sum_maximal_exponential {X : ℕ → Ω → ℝ} {c : ℝ≥0}
    (hX : ∀ i, StronglyMeasurable (X i)) (hind : iIndepFun X μ)
    (hmgf : ∀ i, HasSubgaussianMGF (X i) c μ)
    (hmean : ∀ i, ∫ ω, X i ω ∂μ = 0)
    (m : ℕ) {a t : ℝ} (ht : 0 ≤ t) :
    μ.real {ω | ∃ k ≤ m, a ≤ ∑ i ∈ Finset.range (k + 1), X i ω} ≤
      Real.exp (-t * a + (m + 1) * (c : ℝ) * t ^ 2 / 2) := by
  obtain ⟨F, hs⟩ := exp_partial_sum_submartingale hX hind hmgf hmean t
  let f : ℕ → Ω → ℝ := fun k ω => Real.exp (t * ∑ i ∈ Finset.range (k + 1), X i ω)
  let A : Set Ω := {ω | Real.exp (t * a) ≤
    (Finset.range (m + 1)).sup' Finset.nonempty_range_add_one (fun k => f k ω)}
  have hmax := maximal_ineq (f := f) hs (fun k ω => (Real.exp_pos _).le)
    (ε := ⟨Real.exp (t * a), (Real.exp_pos _).le⟩) m
  have hr := ENNReal.toReal_mono ENNReal.ofReal_ne_top hmax
  have hn : 0 ≤ ∫ ω in A, f m ω ∂μ := integral_nonneg (fun _ => (Real.exp_pos _).le)
  have hr' : Real.exp (t * a) * μ.real A ≤ ∫ ω in A, f m ω ∂μ := by
    rw [ENNReal.toReal_mul] at hr
    change Real.exp (t * a) * μ.real A ≤
      (ENNReal.ofReal (∫ ω in A, f m ω ∂μ)).toReal at hr
    rwa [ENNReal.toReal_ofReal hn] at hr
  have hsubset : {ω | ∃ k ≤ m, a ≤ ∑ i ∈ Finset.range (k + 1), X i ω} ⊆ A := by
    rintro ω ⟨k, hk, hka⟩
    exact (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hka ht)).trans
      (Finset.le_sup' (fun k => f k ω) (Finset.mem_range.mpr (Nat.lt_succ_of_le hk)))
  have htotal : (∫ ω, f m ω ∂μ) ≤
      Real.exp ((m + 1) * (c : ℝ) * t ^ 2 / 2) := by
    have h := (HasSubgaussianMGF.sum_of_iIndepFun hind
      (s := Finset.range (m + 1)) (fun i _ => hmgf i)).mgf_le t
    simpa [f, mgf] using h
  have hbound : Real.exp (t * a) *
      μ.real {ω | ∃ k ≤ m, a ≤ ∑ i ∈ Finset.range (k + 1), X i ω} ≤
      Real.exp ((m + 1) * (c : ℝ) * t ^ 2 / 2) := by
    exact (mul_le_mul_of_nonneg_left (measureReal_mono hsubset) (Real.exp_pos _).le).trans
      (hr'.trans ((setIntegral_le_integral (hs.integrable m)
        (ae_of_all _ (fun _ => (Real.exp_pos _).le))).trans htotal))
  calc
    _ ≤ Real.exp ((m + 1) * (c : ℝ) * t ^ 2 / 2) / Real.exp (t * a) :=
      (le_div_iff₀ (Real.exp_pos _)).mpr (by simpa only [mul_comm] using hbound)
    _ = _ := by rw [← Real.exp_sub]; congr 1; ring

lemma partial_sum_maximal_tail_oai {X : ℕ → Ω → ℝ} {c : ℝ≥0}
    (hX : ∀ i, StronglyMeasurable (X i)) (hind : iIndepFun X μ)
    (hmgf : ∀ i, HasSubgaussianMGF (X i) c μ)
    (hmean : ∀ i, ∫ ω, X i ω ∂μ = 0) (hc : 0 < c)
    (m : ℕ) {a : ℝ} (ha : 0 ≤ a) :
    μ.real {ω | ∃ k ≤ m, a ≤ ∑ i ∈ Finset.range (k + 1), X i ω} ≤
      Real.exp (-a ^ 2 / (2 * (m + 1) * (c : ℝ))) := by
  have hc' : 0 < (c : ℝ) := hc
  have hp : 0 < (m + 1 : ℝ) := by positivity
  have h := partial_sum_maximal_exponential hX hind hmgf hmean m
    (a := a) (t := a / ((m + 1) * (c : ℝ))) (by positivity)
  convert h using 1
  congr 1
  field_simp
  ring

end

end CriticalSK

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.CriticalSK.partial_sum_maximal_tail_oai.{u_1} := @OAI.CriticalSK.partial_sum_maximal_tail_oai.{u_1}
