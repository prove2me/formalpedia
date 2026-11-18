-- Prove2me | solution 1 for LostSalesRQ.operating_transform
-- status  : ACCEPTED   (prove)
-- author  : @Ming Hu
-- created : 2026-11-18T01:44:48.247278+00:00
-- url     : https://prove2.me/submissions/f0dfba88-8abb-4c6a-a95e-e254d3b04169

import Definitions.Def_LostSalesRQ_poisson_functions
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Intervals
import Definitions.Def_LostSalesRQ_poisson_process
import Definitions.Def_LostSalesRQ_lower_curve
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Probability.CDF
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.MetricSpace.Lipschitz
import Definitions.Def_LostSalesRQ_model
import Mathlib.Probability.Distributions.Poisson.Basic
import Mathlib.Probability.Independence.Integration
import Mathlib.MeasureTheory.Function.Floor

namespace LostSalesRQ
open Finset

lemma pm_pos {μ : ℝ} (hμ : 0 < μ) (j : ℕ) : 0 < poisMass μ j := by
  unfold poisMass; positivity

lemma pm_succ (μ : ℝ) (j : ℕ) :
    poisMass μ (j + 1) * ((j : ℝ) + 1) = μ * poisMass μ j := by
  unfold poisMass
  rw [Nat.factorial_succ]
  push_cast
  have hf : (Nat.factorial j : ℝ) ≠ 0 := by positivity
  have hj : (j : ℝ) + 1 ≠ 0 := by positivity
  field_simp
  ring

lemma pc_succ (μ : ℝ) (j : ℕ) : poisCdf μ (j + 1) = poisCdf μ j + poisMass μ (j + 1) := by
  unfold poisCdf; rw [Finset.sum_range_succ]

lemma pc_zero (μ : ℝ) : poisCdf μ 0 = poisMass μ 0 := by simp [poisCdf]

lemma pm_le_pc {μ : ℝ} (hμ : 0 < μ) (j : ℕ) : poisMass μ j ≤ poisCdf μ j := by
  unfold poisCdf
  exact Finset.single_le_sum (fun i _ => (pm_pos hμ i).le) (Finset.self_mem_range_succ j)

lemma pc_pos {μ : ℝ} (hμ : 0 < μ) (j : ℕ) : 0 < poisCdf μ j :=
  lt_of_lt_of_le (pm_pos hμ j) (pm_le_pc hμ j)

lemma sum_i_pm (μ : ℝ) (j : ℕ) :
    ∑ i ∈ range (j + 1), (i : ℝ) * poisMass μ i = μ * (poisCdf μ j - poisMass μ j) := by
  induction j with
  | zero => simp [poisCdf]
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, pc_succ]
    have h := pm_succ μ n
    push_cast
    linear_combination h

lemma sum_ii_pm (μ : ℝ) (j : ℕ) :
    ∑ i ∈ range (j + 1), (i : ℝ) * ((i : ℝ) - 1) * poisMass μ i
      = μ ^ 2 * (poisCdf μ j - poisMass μ j) - μ * (j : ℝ) * poisMass μ j := by
  induction j with
  | zero => simp [poisCdf]
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, pc_succ]
    have h := pm_succ μ n
    push_cast
    linear_combination ((n : ℝ) + μ) * h

lemma lf_pos {μ : ℝ} (hμ : 0 < μ) (j : ℕ) : 0 < lossFraction μ j := by
  unfold lossFraction; exact div_pos (pm_pos hμ j) (pc_pos hμ j)

lemma lf_le_one {μ : ℝ} (hμ : 0 < μ) (j : ℕ) : lossFraction μ j ≤ 1 := by
  unfold lossFraction; rw [div_le_one (pc_pos hμ j)]; exact pm_le_pc hμ j

lemma moh_mul_pc {μ : ℝ} (hμ : 0 < μ) (j : ℕ) :
    meanOnHand μ j * poisCdf μ j = ∑ i ∈ range (j + 1), ((j : ℝ) - (i : ℝ)) * poisMass μ i := by
  have hF := pc_pos hμ j
  have h1 := sum_i_pm μ j
  have h0 : ∑ i ∈ range (j + 1), ((j : ℝ) - (i : ℝ)) * poisMass μ i
      = (j : ℝ) * poisCdf μ j - ∑ i ∈ range (j + 1), (i : ℝ) * poisMass μ i := by
    unfold poisCdf
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl; intro i _; ring
  rw [h0, h1]
  unfold meanOnHand lossFraction
  field_simp
  ring

lemma moh_nonneg {μ : ℝ} (hμ : 0 < μ) (j : ℕ) : 0 ≤ meanOnHand μ j := by
  have hF := pc_pos hμ j
  have h := moh_mul_pc hμ j
  have hs : 0 ≤ ∑ i ∈ range (j + 1), ((j : ℝ) - (i : ℝ)) * poisMass μ i := by
    apply Finset.sum_nonneg
    intro i hi
    have hij : (i : ℝ) ≤ j := by
      have := Finset.mem_range.mp hi
      exact_mod_cast Nat.lt_succ_iff.mp this
    exact mul_nonneg (by linarith) (pm_pos hμ i).le
  by_contra hneg
  push_neg at hneg
  have : meanOnHand μ j * poisCdf μ j < 0 := mul_neg_of_neg_of_pos hneg hF
  linarith

lemma lf_succ {μ : ℝ} (hμ : 0 < μ) (j : ℕ) :
    lossFraction μ (j + 1) = μ * lossFraction μ j / (μ + meanOnHand μ j + 1) := by
  have hF := pc_pos hμ j
  have hp := pm_pos hμ j
  have h := pm_succ μ j
  have hj : (0 : ℝ) < (j : ℝ) + 1 := by positivity
  have hHdef : meanOnHand μ j = (j : ℝ) - μ + μ * lossFraction μ j := rfl
  have hpe : poisMass μ j = lossFraction μ j * poisCdf μ j := by
    unfold lossFraction; field_simp
  have he := lf_pos hμ j
  rw [hHdef]
  set e := lossFraction μ j with he_def
  set F := poisCdf μ j with hF_def
  have hp' : poisMass μ (j + 1) = μ * e * F / ((j : ℝ) + 1) := by
    rw [eq_div_iff hj.ne', h, hpe]; ring
  show poisMass μ (j + 1) / poisCdf μ (j + 1) = _
  rw [pc_succ, hp']
  have h1 : 0 < F + μ * e * F / ((j : ℝ) + 1) := by positivity
  have h2 : 0 < μ + ((j : ℝ) - μ + μ * e) + 1 := by nlinarith
  rw [div_eq_div_iff h1.ne' h2.ne']
  field_simp
  ring

lemma ohv_eq {μ : ℝ} (hμ : 0 < μ) (j : ℕ) :
    onHandVariance μ j = μ * (1 - lossFraction μ j * (meanOnHand μ j + 1)) := by
  have hF := pc_pos hμ j
  have hFne : poisCdf μ j ≠ 0 := hF.ne'
  set H := meanOnHand μ j with hHdef
  -- reflect the sum
  have hrefl : onHandVariance μ j
      = ∑ i ∈ range (j + 1), (((j : ℝ) - (i : ℝ)) - H) ^ 2 * (poisMass μ i / poisCdf μ j) := by
    unfold onHandVariance
    rw [← Finset.sum_range_reflect]
    apply Finset.sum_congr rfl
    intro i hi
    have hij : i ≤ j := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    have h1 : j + 1 - 1 - i = j - i := by omega
    have h2 : j - (j - i) = i := by omega
    rw [h1, h2]
    push_cast [hij]
    ring
  rw [hrefl]
  have hexp : ∀ i ∈ range (j + 1), (((j : ℝ) - (i : ℝ)) - H) ^ 2 * (poisMass μ i / poisCdf μ j)
      = ((((j : ℝ) - H) ^ 2) * poisMass μ i - (2 * ((j : ℝ) - H) - 1) * ((i : ℝ) * poisMass μ i)
          + (i : ℝ) * ((i : ℝ) - 1) * poisMass μ i) / poisCdf μ j := by
    intro i _; field_simp; ring
  rw [Finset.sum_congr rfl hexp, ← Finset.sum_div, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum, sum_i_pm, sum_ii_pm]
  have hFdef : ∑ i ∈ range (j + 1), poisMass μ i = poisCdf μ j := rfl
  rw [hFdef]
  rw [hHdef]
  unfold meanOnHand lossFraction
  field_simp
  ring

lemma en_eq {μ : ℝ} (hμ : 0 < μ) (j : ℕ) : erlangNormalizer μ j = 1 / lossFraction μ j := by
  unfold erlangNormalizer lossFraction
  rw [one_div_div]

end LostSalesRQ

namespace LostSalesRQ

open MeasureTheory ProbabilityTheory Filter Set Topology

instance d2_expProb : IsProbabilityMeasure (expMeasure 1) :=
  isProbabilityMeasure_expMeasure one_pos

instance d2_lawProb : IsProbabilityMeasure interarrivalLaw := by
  unfold interarrivalLaw; infer_instance

/-- Prepend an interarrival time to a demand path. -/
def consPath (p : ℝ × DemandPath) : DemandPath
  | 0 => p.1
  | n + 1 => p.2 n

lemma measurable_consPath : Measurable consPath := by
  rw [measurable_pi_iff]
  intro n
  cases n with
  | zero => exact measurable_fst
  | succ m => exact (measurable_pi_apply m).comp measurable_snd

lemma law_shift_box (n : ℕ) (t : ℕ → Set ℝ) (ht : ∀ i, MeasurableSet (t i)) :
    (((expMeasure 1).prod interarrivalLaw).map consPath) (Set.pi ↑(Finset.range n) t) =
      ∏ i ∈ Finset.range n, expMeasure 1 (t i) := by
  have : IsProbabilityMeasure (((expMeasure 1).prod interarrivalLaw).map consPath) :=
    Measure.isProbabilityMeasure_map measurable_consPath.aemeasurable
  cases n with
  | zero => simp
  | succ m =>
    rw [Measure.map_apply measurable_consPath
      (MeasurableSet.pi (Finset.countable_toSet _) (fun i _ => ht i))]
    have hpre : consPath ⁻¹' Set.pi ↑(Finset.range (m + 1)) t =
        t 0 ×ˢ Set.pi ↑(Finset.range m) (fun j => t (j + 1)) := by
      ext ⟨a, ξ⟩
      simp only [Set.mem_preimage, Set.mem_pi, Finset.mem_coe, Finset.mem_range, Set.mem_prod]
      constructor
      · intro h
        exact ⟨h 0 (Nat.succ_pos m), fun j hj => h (j + 1) (by omega)⟩
      · rintro ⟨h0, h1⟩ i hi
        cases i with
        | zero => exact h0
        | succ j => exact h1 j (by omega)
    rw [hpre, Measure.prod_prod]
    unfold interarrivalLaw
    rw [Measure.infinitePi_pi (fun _ : ℕ => expMeasure 1) (fun i _ => ht (i + 1)),
      Finset.prod_range_succ']
    ring

lemma law_shift : ((expMeasure 1).prod interarrivalLaw).map consPath = interarrivalLaw := by
  refine Measure.eq_infinitePi (fun _ : ℕ => expMeasure 1) ?_
  intro s t ht
  obtain ⟨n, hn⟩ := Finset.exists_nat_subset_range s
  classical
  set t' : ℕ → Set ℝ := fun i => if i ∈ s then t i else univ with ht'
  have h1 : Set.pi (↑s) t = Set.pi (↑(Finset.range n)) t' := by
    ext ξ
    simp only [Set.mem_pi, Finset.mem_coe, ht']
    constructor
    · intro h i _
      by_cases his : i ∈ s
      · simp only [his, if_true]; exact h i his
      · simp only [his, if_false]; exact Set.mem_univ _
    · intro h i his
      have := h i (hn his)
      simpa only [his, if_true] using this
  have h2 : ∏ i ∈ s, expMeasure 1 (t i) = ∏ i ∈ Finset.range n, expMeasure 1 (t' i) := by
    rw [← Finset.prod_subset hn]
    · exact Finset.prod_congr rfl (fun i hi => by simp only [ht', hi, if_true])
    · intro i _ hi
      simp only [ht', hi, if_false, measure_univ]
  rw [h1, h2]
  exact law_shift_box n t' (fun i => by
    by_cases h : i ∈ s
    · simp only [ht', h, if_true]; exact ht i
    · simp only [ht', h, if_false]; exact MeasurableSet.univ)

/-- The crossing event {∃ k < K, f S_k - k > x}. -/
def crossSet (f x : ℝ) (K : ℕ) : Set DemandPath :=
  {ξ | ∃ k < K, x < f * arrivalEpoch ξ k - k}

lemma arrivalEpoch_cons_zero (a : ℝ) (ξ : DemandPath) :
    arrivalEpoch (consPath (a, ξ)) 0 = a := by
  simp [arrivalEpoch, consPath]

lemma arrivalEpoch_cons_succ (a : ℝ) (ξ : DemandPath) (k : ℕ) :
    arrivalEpoch (consPath (a, ξ)) (k + 1) = a + arrivalEpoch ξ k := by
  unfold arrivalEpoch
  rw [Finset.sum_range_succ' _ (k + 1)]
  simp only [consPath]
  ring

lemma measurable_arrivalEpoch (k : ℕ) : Measurable (fun ξ : DemandPath => arrivalEpoch ξ k) := by
  unfold arrivalEpoch
  exact Finset.measurable_sum _ (fun i _ => measurable_pi_apply i)

lemma measurableSet_crossSet (f x : ℝ) (K : ℕ) : MeasurableSet (crossSet f x K) := by
  have : crossSet f x K = ⋃ k ∈ Finset.range K, {ξ | x < f * arrivalEpoch ξ k - k} := by
    ext ξ; simp [crossSet]
  rw [this]
  exact Finset.measurableSet_biUnion _ (fun k _ =>
    measurableSet_lt measurable_const (((measurable_arrivalEpoch k).const_mul f).sub_const _))

lemma crossSet_cons (f x a : ℝ) (K : ℕ) :
    {ξ : DemandPath | consPath (a, ξ) ∈ crossSet f x (K + 1)} =
      if x < f * a then univ else crossSet f (x + 1 - f * a) K := by
  ext ξ
  split_ifs with h
  · simp only [mem_ofPred_eq, mem_univ, iff_true, crossSet]
    exact ⟨0, Nat.succ_pos _, by simpa [arrivalEpoch_cons_zero] using h⟩
  · simp only [crossSet, mem_ofPred_eq]
    constructor
    · rintro ⟨k, hk, hx⟩
      cases k with
      | zero => exact absurd (by simpa [arrivalEpoch_cons_zero] using hx) h
      | succ k =>
        refine ⟨k, by omega, ?_⟩
        rw [arrivalEpoch_cons_succ] at hx
        push_cast at hx
        linarith
    · rintro ⟨k, hk, hx⟩
      refine ⟨k + 1, by omega, ?_⟩
      rw [arrivalEpoch_cons_succ]
      push_cast
      linarith

lemma law_crossSet_succ (f x : ℝ) (K : ℕ) :
    interarrivalLaw (crossSet f x (K + 1)) =
      ∫⁻ a, (if x < f * a then 1 else interarrivalLaw (crossSet f (x + 1 - f * a) K))
        ∂(expMeasure 1) := by
  conv_lhs => rw [← law_shift]
  rw [Measure.map_apply measurable_consPath (measurableSet_crossSet _ _ _),
    Measure.prod_apply (measurable_consPath (measurableSet_crossSet _ _ _))]
  apply lintegral_congr
  intro a
  have : Prod.mk a ⁻¹' (consPath ⁻¹' crossSet f x (K + 1)) =
      {ξ | consPath (a, ξ) ∈ crossSet f x (K + 1)} := rfl
  rw [this, crossSet_cons]
  split_ifs <;> simp

end LostSalesRQ

namespace LostSalesRQ

open MeasureTheory ProbabilityTheory Filter Set Topology

lemma expMeasure_eq_withDensity (r : ℝ) :
    expMeasure r = volume.withDensity (exponentialPDF r) := rfl

lemma measurable_exponentialPDF' (r : ℝ) : Measurable (exponentialPDF r) :=
  (measurable_exponentialPDFReal r).ennreal_ofReal

lemma exp_Iic (r h : ℝ) (hr : 0 < r) (hh : 0 ≤ h) :
    expMeasure r (Iic h) = ENNReal.ofReal (1 - Real.exp (-(r * h))) := by
  have := isProbabilityMeasure_expMeasure hr
  rw [← ofReal_cdf, cdf_expMeasure_eq hr, if_pos hh]

lemma exp_Ioi (h : ℝ) (hh : 0 ≤ h) :
    expMeasure 1 (Ioi h) = ENNReal.ofReal (Real.exp (-h)) := by
  rw [← compl_Iic, prob_compl_eq_one_sub measurableSet_Iic, exp_Iic 1 h one_pos hh, one_mul]
  have h1 : Real.exp (-h) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  rw [ENNReal.ofReal_sub 1 (Real.exp_pos _).le, ENNReal.ofReal_one,
    ENNReal.sub_sub_cancel ENNReal.one_ne_top (ENNReal.ofReal_le_one.mpr h1)]

lemma lint_exp_mul_Iic (c h : ℝ) (hc : c < 1) (hh : 0 ≤ h) :
    ∫⁻ a in Iic h, ENNReal.ofReal (Real.exp (c * a)) ∂(expMeasure 1) =
      ENNReal.ofReal (1 / (1 - c)) * ENNReal.ofReal (1 - Real.exp (-((1 - c) * h))) := by
  have hr : 0 < 1 - c := by linarith
  rw [expMeasure_eq_withDensity, setLIntegral_withDensity_eq_setLIntegral_mul _
    (measurable_exponentialPDF' 1) (by fun_prop) measurableSet_Iic]
  have hpt : ∀ a : ℝ, (exponentialPDF 1 * fun a => ENNReal.ofReal (Real.exp (c * a))) a =
      ENNReal.ofReal (1 / (1 - c)) * exponentialPDF (1 - c) a := by
    intro a
    simp only [Pi.mul_apply]
    rcases lt_or_ge a 0 with ha | ha
    · rw [exponentialPDF_of_neg ha, exponentialPDF_of_neg ha, zero_mul, mul_zero]
    · rw [exponentialPDF_of_nonneg ha, exponentialPDF_of_nonneg ha,
        ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
      congr 1
      have e1 : 1 * Real.exp (-(1 * a)) * Real.exp (c * a) = Real.exp (-((1 - c) * a)) := by
        rw [one_mul, ← Real.exp_add]; congr 1; ring
      have e2 : 1 / (1 - c) * ((1 - c) * Real.exp (-((1 - c) * a))) =
          Real.exp (-((1 - c) * a)) := by
        field_simp
      rw [e1, e2]
  rw [setLIntegral_congr_fun measurableSet_Iic (fun a _ => hpt a),
    lintegral_const_mul _ (measurable_exponentialPDF' _), ← withDensity_apply _ measurableSet_Iic,
    ← expMeasure_eq_withDensity, exp_Iic (1 - c) h hr hh]

lemma cross_step (f lam x : ℝ) (hf : 0 < f) (hlam : 0 < lam) (hr : 0 < 1 - lam * f)
    (hkey : Real.exp (-lam) ≤ 1 - lam * f) (hx : 0 ≤ x) :
    ∫⁻ a, (if x < f * a then 1 else ENNReal.ofReal (Real.exp (-(lam * (x + 1 - f * a)))))
        ∂(expMeasure 1) ≤ ENNReal.ofReal (Real.exp (-(lam * x))) := by
  set h := x / f with hh
  have hh0 : 0 ≤ h := div_nonneg hx hf.le
  have hfh : f * h = x := by rw [hh]; field_simp
  rw [← lintegral_add_compl _ (measurableSet_Ioi (a := h))]
  have e1 : ∫⁻ a in Ioi h, (if x < f * a then 1 else
      ENNReal.ofReal (Real.exp (-(lam * (x + 1 - f * a))))) ∂(expMeasure 1) =
      expMeasure 1 (Ioi h) := by
    rw [setLIntegral_congr_fun measurableSet_Ioi (g := fun _ => (1 : ENNReal)) (fun a ha => by
      have : x < f * a := by
        rw [mem_Ioi] at ha
        nlinarith
      simp [this])]
    simp
  have e2 : ∫⁻ a in (Ioi h)ᶜ, (if x < f * a then 1 else
      ENNReal.ofReal (Real.exp (-(lam * (x + 1 - f * a))))) ∂(expMeasure 1) =
      ENNReal.ofReal (Real.exp (-(lam * (x + 1)))) *
        ∫⁻ a in Iic h, ENNReal.ofReal (Real.exp ((lam * f) * a)) ∂(expMeasure 1) := by
    rw [compl_Ioi, ← lintegral_const_mul _ (by fun_prop)]
    apply setLIntegral_congr_fun measurableSet_Iic
    intro a ha
    have : ¬ x < f * a := by
      rw [mem_Iic] at ha
      nlinarith
    simp only [this, if_false]
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
    congr 2; ring
  rw [e1, e2, exp_Ioi h hh0, lint_exp_mul_Iic (lam * f) h (by linarith) hh0]
  have hq : Real.exp (-((1 - lam * f) * h)) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by nlinarith)
  rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (Real.exp_pos _).le,
    ← ENNReal.ofReal_add (Real.exp_pos _).le
      (mul_nonneg (Real.exp_pos _).le (mul_nonneg (by positivity) (by linarith)))]
  apply ENNReal.ofReal_le_ofReal
  set E := Real.exp (-(lam * x)) with hE
  set u := Real.exp (-lam) with hu
  set q := Real.exp (-((1 - lam * f) * h)) with hqdef
  have hE0 : 0 ≤ E := (Real.exp_pos _).le
  have e3 : Real.exp (-h) = E * q := by
    rw [hE, hqdef, ← Real.exp_add]; congr 1
    have : lam * x = lam * (f * h) := by rw [hfh]
    rw [this]; ring
  have e4 : Real.exp (-(lam * (x + 1))) = E * u := by
    rw [hE, hu, ← Real.exp_add]; congr 1; ring
  rw [e3, e4]
  have hu1 : u * (1 / (1 - lam * f)) ≤ 1 := by
    rw [mul_one_div, div_le_one hr]; exact hkey
  have := mul_le_mul_of_nonneg_left hu1 (mul_nonneg hE0 (sub_nonneg.mpr hq))
  nlinarith

lemma cross_bound (f lam : ℝ) (hf : 0 ≤ f) (hlam : 0 < lam) (hr : 0 < 1 - lam * f)
    (hkey : Real.exp (-lam) ≤ 1 - lam * f) (K : ℕ) (x : ℝ) (hx : 0 ≤ x) :
    interarrivalLaw (crossSet f x K) ≤ ENNReal.ofReal (Real.exp (-(lam * x))) := by
  rcases hf.eq_or_lt with hf0 | hfpos
  · have : crossSet f x K = ∅ := by
      ext ξ
      simp only [crossSet, mem_ofPred_eq, mem_empty_iff_false, iff_false, not_exists, not_and]
      intro k _ hk
      rw [← hf0, zero_mul, zero_sub] at hk
      have : (0:ℝ) ≤ k := Nat.cast_nonneg k
      linarith
    rw [this]; simp
  · induction K generalizing x with
    | zero =>
      have : crossSet f x 0 = ∅ := by ext ξ; simp [crossSet]
      rw [this]; simp
    | succ K ih =>
      rw [law_crossSet_succ]
      refine le_trans (lintegral_mono (fun a => ?_)) (cross_step f lam x hfpos hlam hr hkey hx)
      split_ifs with h
      · exact le_rfl
      · exact ih _ (by push Not at h; linarith)

lemma lint_exp_Ioi (lam : ℝ) (hlam : 0 < lam) :
    ∫⁻ t in Ioi (0:ℝ), ENNReal.ofReal (Real.exp (-(lam * t))) ≤ ENNReal.ofReal (1 / lam) := by
  have hpt : ∀ t ∈ Ioi (0:ℝ), ENNReal.ofReal (Real.exp (-(lam * t))) =
      ENNReal.ofReal (1 / lam) * exponentialPDF lam t := by
    intro t ht
    rw [exponentialPDF_of_nonneg (le_of_lt ht), ← ENNReal.ofReal_mul (by positivity)]
    congr 1; field_simp
  rw [setLIntegral_congr_fun measurableSet_Ioi hpt,
    lintegral_const_mul _ (measurable_exponentialPDF' _)]
  calc ENNReal.ofReal (1 / lam) * ∫⁻ t in Ioi 0, exponentialPDF lam t
      ≤ ENNReal.ofReal (1 / lam) * ∫⁻ t, exponentialPDF lam t := by
        gcongr; exact Measure.restrict_le_self
    _ = ENNReal.ofReal (1 / lam) := by rw [lintegral_exponentialPDF_eq_one hlam, mul_one]

end LostSalesRQ

namespace LostSalesRQ

open MeasureTheory ProbabilityTheory Filter Set Topology

lemma pdf_mul_exp (c : ℝ) (hc : c < 1) (a : ℝ) :
    exponentialPDF 1 a * ENNReal.ofReal (Real.exp (c * a)) =
      ENNReal.ofReal (1 / (1 - c)) * exponentialPDF (1 - c) a := by
  have hr : 0 < 1 - c := by linarith
  rcases lt_or_ge a 0 with ha | ha
  · rw [exponentialPDF_of_neg ha, exponentialPDF_of_neg ha, zero_mul, mul_zero]
  · rw [exponentialPDF_of_nonneg ha, exponentialPDF_of_nonneg ha,
      ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    have e1 : 1 * Real.exp (-(1 * a)) * Real.exp (c * a) = Real.exp (-((1 - c) * a)) := by
      rw [one_mul, ← Real.exp_add]; congr 1; ring
    have e2 : 1 / (1 - c) * ((1 - c) * Real.exp (-((1 - c) * a))) =
        Real.exp (-((1 - c) * a)) := by
      field_simp
    rw [e1, e2]

lemma lint_exp_mul (c : ℝ) (hc : c < 1) :
    ∫⁻ a, ENNReal.ofReal (Real.exp (c * a)) ∂(expMeasure 1) = ENNReal.ofReal (1 / (1 - c)) := by
  rw [expMeasure_eq_withDensity, lintegral_withDensity_eq_lintegral_mul _
    (measurable_exponentialPDF' 1) (by fun_prop)]
  simp only [Pi.mul_apply, pdf_mul_exp c hc]
  rw [lintegral_const_mul _ (measurable_exponentialPDF' _),
    lintegral_exponentialPDF_eq_one (by linarith), mul_one]

lemma law_coord_neg (i : ℕ) : interarrivalLaw {ξ : DemandPath | ξ i < 0} = 0 := by
  have hmap : interarrivalLaw.map (fun ξ : DemandPath => ξ i) = expMeasure 1 := by
    unfold interarrivalLaw; exact Measure.infinitePi_map_eval (fun _ : ℕ => expMeasure 1) i
  have : {ξ : DemandPath | ξ i < 0} = (fun ξ : DemandPath => ξ i) ⁻¹' Iio 0 := rfl
  rw [this, ← Measure.map_apply (measurable_pi_apply i) measurableSet_Iio, hmap,
    expMeasure_eq_withDensity, withDensity_apply _ measurableSet_Iio]
  exact lintegral_exponentialPDF_of_nonpos le_rfl

/-- Partial sums ξ 0 + ⋯ + ξ (n-1). -/
def psum (ξ : DemandPath) (n : ℕ) : ℝ := ∑ i ∈ Finset.range n, ξ i

lemma psum_cons (a : ℝ) (ξ : DemandPath) (n : ℕ) :
    psum (consPath (a, ξ)) (n + 1) = a + psum ξ n := by
  unfold psum; rw [Finset.sum_range_succ']; simp only [consPath]; ring

lemma measurable_psum (n : ℕ) : Measurable (fun ξ : DemandPath => psum ξ n) := by
  unfold psum
  exact Finset.measurable_sum _ (fun i _ => measurable_pi_apply i)

lemma lint_exp_neg_psum (n : ℕ) :
    ∫⁻ ξ, ENNReal.ofReal (Real.exp (-psum ξ n)) ∂interarrivalLaw = ENNReal.ofReal (1 / 2) ^ n := by
  induction n with
  | zero => simp [psum]
  | succ n ih =>
    have hm : Measurable (fun ξ : DemandPath => ENNReal.ofReal (Real.exp (-psum ξ (n + 1)))) :=
      (measurable_psum (n + 1)).neg.exp.ennreal_ofReal
    conv_lhs => rw [← law_shift]
    rw [lintegral_map hm measurable_consPath]
    have hpt : ∀ p : ℝ × DemandPath, ENNReal.ofReal (Real.exp (-psum (consPath p) (n + 1))) =
        ENNReal.ofReal (Real.exp ((-1) * p.1)) * ENNReal.ofReal (Real.exp (-psum p.2 n)) := by
      rintro ⟨a, ξ⟩
      rw [psum_cons, ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]; congr 2; ring
    simp only [hpt]
    rw [lintegral_prod_mul (f := fun a => ENNReal.ofReal (Real.exp ((-1) * a)))
      (g := fun ξ => ENNReal.ofReal (Real.exp (-psum ξ n))) (by fun_prop)
      ((measurable_psum n).neg.exp.ennreal_ofReal.aemeasurable), ih,
      lint_exp_mul (-1) (by norm_num), pow_succ]
    norm_num
    ring

lemma law_noexplode (T : ℝ) : interarrivalLaw {ξ : DemandPath | ∀ K, arrivalEpoch ξ K ≤ T} = 0 := by
  refine le_antisymm ?_ zero_le
  apply ENNReal.le_of_forall_pos_le_add
  intro ε hε _
  rw [zero_add]
  have hε' : (0:ℝ) < ε := hε
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (div_pos hε' (Real.exp_pos T)) (by norm_num : (1/2:ℝ) < 1)
  have hsub : {ξ : DemandPath | ∀ K, arrivalEpoch ξ K ≤ T} ⊆
      {ξ | ENNReal.ofReal (Real.exp (-T)) ≤ ENNReal.ofReal (Real.exp (-psum ξ (n + 1)))} := by
    intro ξ hξ
    simp only [mem_ofPred_eq] at hξ ⊢
    apply ENNReal.ofReal_le_ofReal
    apply Real.exp_le_exp.mpr
    have := hξ n
    unfold arrivalEpoch at this
    unfold psum
    linarith
  have hm : Measurable (fun ξ : DemandPath => ENNReal.ofReal (Real.exp (-psum ξ (n + 1)))) :=
    (measurable_psum (n + 1)).neg.exp.ennreal_ofReal
  have hmk := mul_meas_ge_le_lintegral₀ (hm.aemeasurable (μ := interarrivalLaw))
    (ENNReal.ofReal (Real.exp (-T)))
  beta_reduce at hmk
  rw [lint_exp_neg_psum] at hmk
  have h1 : ENNReal.ofReal (Real.exp (-T)) * interarrivalLaw {ξ : DemandPath | ∀ K, arrivalEpoch ξ K ≤ T}
      ≤ ENNReal.ofReal (1 / 2) ^ (n + 1) := le_trans (by gcongr) hmk
  have hpos : ENNReal.ofReal (Real.exp (-T)) ≠ 0 := by
    rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]; exact Real.exp_pos _
  have hfin : ENNReal.ofReal (Real.exp (-T)) ≠ ⊤ := ENNReal.ofReal_ne_top
  calc interarrivalLaw {ξ : DemandPath | ∀ K, arrivalEpoch ξ K ≤ T}
      = (ENNReal.ofReal (Real.exp (-T)))⁻¹ * (ENNReal.ofReal (Real.exp (-T)) *
          interarrivalLaw {ξ : DemandPath | ∀ K, arrivalEpoch ξ K ≤ T}) := by
        rw [← mul_assoc, ENNReal.inv_mul_cancel hpos hfin, one_mul]
    _ ≤ (ENNReal.ofReal (Real.exp (-T)))⁻¹ * ENNReal.ofReal (1 / 2) ^ (n + 1) := by gcongr
    _ = ENNReal.ofReal (Real.exp T * (1 / 2) ^ (n + 1)) := by
        rw [← ENNReal.ofReal_inv_of_pos (Real.exp_pos _), ← ENNReal.ofReal_pow (by norm_num),
          ← ENNReal.ofReal_mul (by positivity), ← Real.exp_neg, neg_neg]
    _ ≤ ε := by
        rw [← ENNReal.ofReal_coe_nnreal]
        apply ENNReal.ofReal_le_ofReal
        have h2 : (1 / 2 : ℝ) ^ (n + 1) ≤ (1 / 2) ^ n :=
          pow_le_pow_of_le_one (by norm_num) (by norm_num) (Nat.le_succ n)
        have h3 := (lt_div_iff₀' (Real.exp_pos T)).mp hn
        nlinarith [Real.exp_pos T]

/-- The exceptional set of demand paths. -/
def badSet (T : ℝ) : Set DemandPath :=
  {ξ | ¬ ((∀ i, 0 ≤ ξ i) ∧ ∃ K, T < arrivalEpoch ξ K)}

lemma law_badSet (T : ℝ) : interarrivalLaw (badSet T) = 0 := by
  have hsub : badSet T ⊆ (⋃ i, {ξ : DemandPath | ξ i < 0}) ∪
      {ξ : DemandPath | ∀ K, arrivalEpoch ξ K ≤ T} := by
    intro ξ hξ
    simp only [badSet, mem_ofPred_eq, not_and_or, not_forall, not_exists, not_le, not_lt] at hξ
    rcases hξ with ⟨i, hi⟩ | h
    · left; exact mem_iUnion.mpr ⟨i, hi⟩
    · right; exact h
  refine le_antisymm ?_ zero_le
  calc interarrivalLaw (badSet T) ≤ _ := measure_mono hsub
    _ ≤ interarrivalLaw (⋃ i, {ξ : DemandPath | ξ i < 0}) +
        interarrivalLaw {ξ : DemandPath | ∀ K, arrivalEpoch ξ K ≤ T} := measure_union_le _ _
    _ = 0 := by rw [measure_iUnion_null (fun i => law_coord_neg i), law_noexplode, add_zero]

lemma maxExcess_gt (T f x : ℝ) (hf : 0 ≤ f) (hx : 0 ≤ x) (ξ : DemandPath)
    (hpos : ∀ i, 0 ≤ ξ i) (hK : ∃ K, T < arrivalEpoch ξ K) (hlt : x < maxExcess T f ξ) :
    ∃ k, x < f * arrivalEpoch ξ k - k := by
  unfold maxExcess at hlt
  rcases (Icc 0 T).eq_empty_or_nonempty with he | hne
  · rw [he, image_empty, Real.sSup_empty] at hlt; linarith
  · obtain ⟨y, ⟨t, ⟨ht0, htT⟩, rfl⟩, hy⟩ := exists_lt_of_lt_csSup (hne.image _) hlt
    have hmono : Monotone (arrivalEpoch ξ) := by
      apply monotone_nat_of_le_succ; intro k; unfold arrivalEpoch
      rw [Finset.sum_range_succ _ (k + 1)]; linarith [hpos (k + 1)]
    obtain ⟨K, hK⟩ := hK
    set D := {k : ℕ | arrivalEpoch ξ k ≤ t} with hD
    have hDfin : D.Finite := by
      apply (Set.finite_lt_nat K).subset
      intro k hk
      simp only [hD, mem_ofPred_eq] at hk
      simp only [mem_ofPred_eq]
      by_contra hkK; push Not at hkK
      have := hmono hkK
      linarith
    set m := D.ncard with hm
    have hmD : m ∉ D := by
      intro hmem
      have hsub : (↑(Finset.range (m + 1)) : Set ℕ) ⊆ D := by
        intro j hj
        simp only [Finset.coe_range, mem_Iio] at hj
        simp only [hD, mem_ofPred_eq] at hmem ⊢
        exact le_trans (hmono (by omega)) hmem
      have := Set.ncard_le_ncard hsub hDfin
      rw [Set.ncard_coe_finset, Finset.card_range] at this
      omega
    refine ⟨m, ?_⟩
    have htm : t < arrivalEpoch ξ m := by
      simp only [hD, mem_ofPred_eq, not_le] at hmD; exact hmD
    have hN : (unitCount ξ t : ℝ) = m := rfl
    beta_reduce at hy
    rw [hN] at hy
    nlinarith

lemma expectedMaxExcess_le (T f lam : ℝ) (hf : 0 ≤ f) (hlam : 0 < lam) (hr : 0 < 1 - lam * f)
    (hkey : Real.exp (-lam) ≤ 1 - lam * f) :
    ∫ ξ, maxExcess T f ξ ∂interarrivalLaw ≤ 1 / lam := by
  by_cases hint : Integrable (fun ξ => maxExcess T f ξ) interarrivalLaw
  swap
  · rw [integral_undef hint]; positivity
  have htail : ∀ t : ℝ, 0 < t → interarrivalLaw {ξ | t < maxExcess T f ξ} ≤
      ENNReal.ofReal (Real.exp (-(lam * t))) := by
    intro t ht
    calc interarrivalLaw {ξ | t < maxExcess T f ξ}
        ≤ interarrivalLaw ((⋃ K, crossSet f t K) ∪ badSet T) := by
          apply measure_mono
          intro ξ hξ
          by_cases hg : (∀ i, 0 ≤ ξ i) ∧ ∃ K, T < arrivalEpoch ξ K
          · left
            obtain ⟨k, hk⟩ := maxExcess_gt T f t hf ht.le ξ hg.1 hg.2 hξ
            exact mem_iUnion.mpr ⟨k + 1, k, Nat.lt_succ_self k, hk⟩
          · right; exact hg
      _ ≤ interarrivalLaw (⋃ K, crossSet f t K) + interarrivalLaw (badSet T) :=
          measure_union_le _ _
      _ = ⨆ K, interarrivalLaw (crossSet f t K) := by
          rw [law_badSet, add_zero]
          apply Monotone.measure_iUnion
          intro K L hKL ξ hξ
          obtain ⟨k, hk, h⟩ := hξ
          exact ⟨k, lt_of_lt_of_le hk hKL, h⟩
      _ ≤ _ := iSup_le (fun K => cross_bound f lam hf hlam hr hkey K t ht.le)
  have hpi := hint.pos_part
  calc ∫ ξ, maxExcess T f ξ ∂interarrivalLaw ≤ ∫ ξ, max (maxExcess T f ξ) 0 ∂interarrivalLaw :=
        integral_mono hint hpi (fun ξ => le_max_left _ _)
    _ = (∫⁻ ξ, ENNReal.ofReal (max (maxExcess T f ξ) 0) ∂interarrivalLaw).toReal :=
        integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall (fun ξ => le_max_right _ _))
          hpi.aestronglyMeasurable
    _ ≤ 1 / lam := by
        apply ENNReal.toReal_le_of_le_ofReal (by positivity)
        rw [lintegral_eq_lintegral_meas_lt (f := fun ξ => max (maxExcess T f ξ) 0) _
          (Eventually.of_forall (fun ξ => le_max_right _ _)) hpi.aemeasurable]
        calc ∫⁻ t in Ioi 0, interarrivalLaw {ξ | t < max (maxExcess T f ξ) 0}
            ≤ ∫⁻ t in Ioi 0, ENNReal.ofReal (Real.exp (-(lam * t))) := by
              apply setLIntegral_mono' measurableSet_Ioi
              intro t ht
              have : {ξ | t < max (maxExcess T f ξ) 0} = {ξ | t < maxExcess T f ξ} := by
                ext ξ
                simp only [mem_ofPred_eq, lt_max_iff]
                constructor
                · rintro (h | h)
                  · exact h
                  · exact absurd h (not_lt.mpr (le_of_lt ht))
                · intro h; exact Or.inl h
              rw [this]; exact htail t ht
          _ ≤ ENNReal.ofReal (1 / lam) := lint_exp_Ioi lam hlam

end LostSalesRQ

namespace LostSalesRQ

open MeasureTheory ProbabilityTheory Filter Set Topology

lemma d2_pm_nonneg (t : ℝ) (ht : 0 ≤ t) (i : ℕ) : 0 ≤ poisMass t i := by
  unfold poisMass; positivity

lemma d2_pm_le_one (t : ℝ) (ht : 0 ≤ t) (i : ℕ) : poisMass t i ≤ 1 := by
  unfold poisMass
  have h := Real.pow_div_factorial_le_exp t ht i
  rw [mul_div_assoc]
  calc Real.exp (-t) * (t ^ i / (i.factorial : ℝ)) ≤ Real.exp (-t) * Real.exp t :=
        mul_le_mul_of_nonneg_left h (Real.exp_pos _).le
    _ = 1 := by rw [← Real.exp_add]; simp

lemma aging_term_le (η T τ : ℝ) (hη : 0 ≤ η) (hτ0 : 0 ≤ τ) (hτT : τ ≤ T) (i : ℕ) :
    η * poisMass τ i - poisCdf τ i ≤ if (i : ℝ) ≤ η * T then η else 0 := by
  have hcdf : 0 ≤ poisCdf τ i := Finset.sum_nonneg (fun j _ => d2_pm_nonneg τ hτ0 j)
  split_ifs with hi
  · have := d2_pm_le_one τ hτ0 i
    nlinarith
  · push Not at hi
    cases i with
    | zero =>
      simp only [Nat.cast_zero] at hi
      nlinarith
    | succ j =>
      have h1 : poisMass τ j ≤ poisCdf τ (j + 1) := by
        unfold poisCdf
        exact Finset.single_le_sum (fun k _ => d2_pm_nonneg τ hτ0 k)
          (Finset.mem_range.mpr (by omega))
      have h2 : poisMass τ (j + 1) * ((j : ℝ) + 1) = τ * poisMass τ j := pm_succ τ j
      have hj : η * τ ≤ (j : ℝ) + 1 := by push_cast at hi; nlinarith
      have hp : 0 ≤ poisMass τ j := d2_pm_nonneg τ hτ0 j
      have hj1 : (0:ℝ) < (j:ℝ) + 1 := by positivity
      have h3 : η * poisMass τ (j + 1) * ((j:ℝ) + 1) ≤ poisMass τ j * ((j:ℝ) + 1) := by
        calc η * poisMass τ (j + 1) * ((j:ℝ) + 1) = η * τ * poisMass τ j := by
              rw [mul_assoc, h2]; ring
          _ ≤ ((j:ℝ) + 1) * poisMass τ j := mul_le_mul_of_nonneg_right hj hp
          _ = poisMass τ j * ((j:ℝ) + 1) := by ring
      have h4 : η * poisMass τ (j + 1) ≤ poisMass τ j := le_of_mul_le_mul_right h3 hj1
      linarith

lemma rank_V (T η : ℝ) (l : ℕ) :
    expectedShortfall T l + η * poisTail T l =
      η - ∑ n ∈ Finset.range l, (η * poisMass T n - poisCdf T n) := by
  induction l with
  | zero => simp [expectedShortfall, poisTail]
  | succ l ih =>
    have hG : expectedShortfall T (l + 1) = expectedShortfall T l + poisCdf T l := by
      unfold expectedShortfall poisCdf
      rw [Finset.sum_range_succ _ (l + 1)]
      push_cast
      simp only [sub_self, zero_mul, add_zero]
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl; intro i _; ring
    have hP : poisTail T (l + 1) = poisTail T l - poisMass T l := by
      unfold poisTail; rw [Finset.sum_range_succ]; ring
    rw [hG, hP, Finset.sum_range_succ]
    linarith [ih]

/-- p_{n-1}(t), with p_{-1} = 0. -/
noncomputable def pPrev : ℕ → ℝ → ℝ
  | 0, _ => 0
  | k + 1, t => poisMass t k

lemma pPrev_mul (t : ℝ) (n : ℕ) : t * pPrev n t = n * poisMass t n := by
  cases n with
  | zero => simp [pPrev]
  | succ k =>
    simp only [pPrev]
    have := pm_succ t k
    push_cast
    linarith

lemma pPrev_nonneg (t : ℝ) (ht : 0 ≤ t) (n : ℕ) : 0 ≤ pPrev n t := by
  cases n with
  | zero => simp [pPrev]
  | succ k => exact d2_pm_nonneg t ht k

lemma hasDerivAt_pm (n : ℕ) (t : ℝ) :
    HasDerivAt (fun s => poisMass s n) (pPrev n t - poisMass t n) t := by
  unfold poisMass
  cases n with
  | zero =>
    have h := (hasDerivAt_neg t).exp
    have hfun : (fun s : ℝ => Real.exp (-s) * s ^ 0 / ((Nat.factorial 0 : ℕ) : ℝ)) =
        fun s => Real.exp (-s) := by
      funext s; simp
    rw [hfun]
    exact h.congr_deriv (by simp [pPrev])
  | succ k =>
    have h1 := (hasDerivAt_neg t).exp
    have h2 := hasDerivAt_pow (k + 1) t
    have h3 := (h1.mul h2).div_const ((k + 1).factorial : ℝ)
    refine h3.congr_deriv ?_
    simp only [pPrev, poisMass, Nat.add_sub_cancel]
    rw [Nat.factorial_succ]
    push_cast
    have hk : ((k.factorial : ℕ) : ℝ) ≠ 0 := by positivity
    field_simp
    ring

lemma hasDerivAt_pc (n : ℕ) (t : ℝ) :
    HasDerivAt (fun s => poisCdf s n) (-poisMass t n) t := by
  induction n with
  | zero =>
    have := hasDerivAt_pm 0 t
    simp only [pPrev, zero_sub] at this
    convert this using 1
    funext s; exact pc_zero s
  | succ k ih =>
    have h := ih.add (hasDerivAt_pm (k + 1) t)
    have hfun : (fun s => poisCdf s (k + 1)) =
        fun s => poisCdf s k + poisMass s (k + 1) := by
      funext s; exact pc_succ s k
    rw [hfun]
    exact h.congr_deriv (by simp only [pPrev]; ring)

lemma continuous_pm (n : ℕ) : Continuous (fun s => poisMass s n) :=
  continuous_iff_continuousAt.mpr (fun t => (hasDerivAt_pm n t).continuousAt)

lemma continuous_pPrev (n : ℕ) : Continuous (pPrev n) := by
  cases n with
  | zero => exact continuous_const
  | succ k => exact continuous_pm k

lemma continuous_pc (n : ℕ) : Continuous (fun s => poisCdf s n) :=
  continuous_iff_continuousAt.mpr (fun t => (hasDerivAt_pc n t).continuousAt)

/-- The rank aging term w_n(τ) = η p_n(τ) - F_n(τ). -/
noncomputable def wfun (η : ℝ) (n : ℕ) (t : ℝ) : ℝ := η * poisMass t n - poisCdf t n

lemma hasDerivAt_wfun (η : ℝ) (n : ℕ) (t : ℝ) :
    HasDerivAt (wfun η n) (η * (pPrev n t - poisMass t n) + poisMass t n) t := by
  have h := ((hasDerivAt_pm n t).const_mul η).sub (hasDerivAt_pc n t)
  exact h.congr_deriv (by ring)

lemma wfun_deriv_mul (η : ℝ) (n : ℕ) (t : ℝ) :
    t * (η * (pPrev n t - poisMass t n) + poisMass t n) =
      poisMass t n * (η * n - (η - 1) * t) := by
  have := pPrev_mul t n
  linear_combination η * this

lemma wfun_monotoneOn (η : ℝ) (n : ℕ) (a b : ℝ) (ha : 0 ≤ a)
    (h : ∀ t ∈ Ioo a b, (η - 1) * t ≤ η * n) : MonotoneOn (wfun η n) (Icc a b) := by
  apply monotoneOn_of_deriv_nonneg (convex_Icc a b)
  · exact fun t _ => (hasDerivAt_wfun η n t).continuousAt.continuousWithinAt
  · exact fun t _ => (hasDerivAt_wfun η n t).differentiableAt.differentiableWithinAt
  · intro t ht
    rw [interior_Icc] at ht
    rw [(hasDerivAt_wfun η n t).deriv]
    have ht0 : 0 < t := lt_of_le_of_lt ha ht.1
    have hs := wfun_deriv_mul η n t
    have hp : 0 ≤ poisMass t n := d2_pm_nonneg t ht0.le n
    have hc := h t ht
    by_contra hneg
    push Not at hneg
    have h1 : t * (η * (pPrev n t - poisMass t n) + poisMass t n) < 0 :=
      mul_neg_of_pos_of_neg ht0 hneg
    have h2 : 0 ≤ poisMass t n * (η * n - (η - 1) * t) := mul_nonneg hp (by linarith)
    linarith

lemma wfun_antitoneOn (η : ℝ) (n : ℕ) (a b : ℝ) (ha : 0 ≤ a)
    (h : ∀ t ∈ Ioo a b, η * n ≤ (η - 1) * t) : AntitoneOn (wfun η n) (Icc a b) := by
  apply antitoneOn_of_deriv_nonpos (convex_Icc a b)
  · exact fun t _ => (hasDerivAt_wfun η n t).continuousAt.continuousWithinAt
  · exact fun t _ => (hasDerivAt_wfun η n t).differentiableAt.differentiableWithinAt
  · intro t ht
    rw [interior_Icc] at ht
    rw [(hasDerivAt_wfun η n t).deriv]
    have ht0 : 0 < t := lt_of_le_of_lt ha ht.1
    have hs := wfun_deriv_mul η n t
    have hp : 0 ≤ poisMass t n := d2_pm_nonneg t ht0.le n
    have hc := h t ht
    by_contra hpos
    push Not at hpos
    have h1 : 0 < t * (η * (pPrev n t - poisMass t n) + poisMass t n) := mul_pos ht0 hpos
    have h2 : poisMass t n * (η * n - (η - 1) * t) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hp (by linarith)
    linarith

/-- The maximizing residual time τ*_n = n/f if n < fμ, and μ otherwise. -/
noncomputable def tauStar (η μ : ℝ) (n : ℕ) : ℝ :=
  if (n : ℝ) < (1 - 1 / η) * μ then n / (1 - 1 / η) else μ

lemma tauStar_mem (η μ : ℝ) (hη : 1 ≤ η) (hμ : 0 ≤ μ) (n : ℕ) :
    0 ≤ tauStar η μ n ∧ tauStar η μ n ≤ μ := by
  unfold tauStar
  split_ifs with h
  · have hf : 0 < 1 - 1 / η := by
      by_contra hf; push Not at hf
      have : (1 - 1 / η) * μ ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hf hμ
      have : (0:ℝ) ≤ n := Nat.cast_nonneg n
      linarith
    refine ⟨div_nonneg (Nat.cast_nonneg n) hf.le, ?_⟩
    rw [div_le_iff₀ hf]; linarith
  · exact ⟨hμ, le_rfl⟩

lemma tauStar_mono (η μ : ℝ) (hη : 1 ≤ η) (hμ : 0 ≤ μ) : Monotone (tauStar η μ) := by
  intro n n' hnn'
  have hc : (n : ℝ) ≤ n' := by exact_mod_cast hnn'
  unfold tauStar
  split_ifs with h1 h2 h2
  · have hf : 0 < 1 - 1 / η := by
      by_contra hf; push Not at hf
      have : (1 - 1 / η) * μ ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hf hμ
      have : (0:ℝ) ≤ n := Nat.cast_nonneg n
      linarith
    exact div_le_div_of_nonneg_right hc hf.le
  · have hf : 0 < 1 - 1 / η := by
      by_contra hf; push Not at hf
      have : (1 - 1 / η) * μ ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hf hμ
      have : (0:ℝ) ≤ n := Nat.cast_nonneg n
      linarith
    rw [div_le_iff₀ hf]; linarith
  · exfalso; linarith
  · exact le_rfl

lemma wfun_le_tauStar (η μ : ℝ) (hη : 1 ≤ η) (hμ : 0 ≤ μ) (n : ℕ) (τ : ℝ) (hτ0 : 0 ≤ τ)
    (hτμ : τ ≤ μ) : wfun η n τ ≤ wfun η n (tauStar η μ n) := by
  have hη0 : 0 < η := by linarith
  have hfη : η * (1 - 1 / η) = η - 1 := by field_simp
  unfold tauStar
  split_ifs with h
  · have hf : 0 < 1 - 1 / η := by
      by_contra hf; push Not at hf
      have : (1 - 1 / η) * μ ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hf hμ
      have : (0:ℝ) ≤ n := Nat.cast_nonneg n
      linarith
    set f := 1 - 1 / η with hfdef
    have hnf : (n : ℝ) / f < μ := by rw [div_lt_iff₀ hf]; linarith
    have hnf0 : 0 ≤ (n : ℝ) / f := div_nonneg (Nat.cast_nonneg n) hf.le
    rcases le_total τ (n / f) with hτ | hτ
    · apply wfun_monotoneOn η n 0 (n / f) le_rfl _ ⟨hτ0, hτ⟩ ⟨hnf0, le_rfl⟩ hτ
      intro t ht
      have : t < n / f := ht.2
      rw [lt_div_iff₀ hf] at this
      nlinarith
    · apply wfun_antitoneOn η n (n / f) μ hnf0 _ ⟨le_rfl, hnf.le⟩ ⟨hτ, hτμ⟩ hτ
      intro t ht
      have : n / f < t := ht.1
      rw [div_lt_iff₀ hf] at this
      nlinarith
  · push Not at h
    apply wfun_monotoneOn η n 0 μ le_rfl _ ⟨hτ0, hτμ⟩ ⟨hμ, le_rfl⟩ hτμ
    intro t ht
    have hf0 : 0 ≤ 1 - 1 / η := by
      rw [sub_nonneg, div_le_one hη0]; exact hη
    have : (1 - 1 / η) * t ≤ (1 - 1 / η) * μ := mul_le_mul_of_nonneg_left ht.2.le hf0
    have h1 : η * ((1 - 1 / η) * t) ≤ η * n := mul_le_mul_of_nonneg_left (this.trans h) hη0.le
    have h2 : η * ((1 - 1 / η) * t) = (η - 1) * t := by rw [← mul_assoc, hfη]
    linarith

end LostSalesRQ

namespace LostSalesRQ

open MeasureTheory ProbabilityTheory Filter Set Topology

/-- Regular counting path: nondecreasing and right-continuous (piecewise constant). -/
def RegPath (f : ℝ → ℕ) : Prop :=
  Monotone f ∧ ∀ t, ∃ δ > 0, ∀ s, t ≤ s → s < t + δ → f s = f t

section paths

variable {f : ℝ → ℕ}

lemma leftLim_bdd (hf : Monotone f) (t : ℝ) : BddAbove (f '' Iio t) :=
  ⟨f t, by rintro _ ⟨s, hs, rfl⟩; exact hf (le_of_lt hs)⟩

lemma leftLim_le_self (hf : Monotone f) (t : ℝ) : leftLim f t ≤ f t :=
  csSup_le ((nonempty_Iio).image _) (by rintro _ ⟨s, hs, rfl⟩; exact hf (le_of_lt hs))

lemma le_leftLim (hf : Monotone f) {s t : ℝ} (hst : s < t) : f s ≤ leftLim f t :=
  le_csSup (leftLim_bdd hf t) ⟨s, hst, rfl⟩

lemma leftLim_attained (hf : Monotone f) (t : ℝ) :
    ∃ s0 < t, ∀ s, s0 ≤ s → s < t → f s = leftLim f t := by
  obtain ⟨s0, hs0, he⟩ := Nat.sSup_mem ((nonempty_Iio (a := t)).image f) (leftLim_bdd hf t)
  refine ⟨s0, hs0, fun s hs1 hs2 => le_antisymm (le_leftLim hf hs2) ?_⟩
  unfold leftLim; rw [← he]; exact hf hs1

lemma leftLim_mono (hf : Monotone f) : Monotone (leftLim f) := by
  intro a b hab
  obtain ⟨s0, hs0, he⟩ := leftLim_attained hf a
  rw [← he s0 le_rfl hs0]
  exact le_leftLim hf (lt_of_lt_of_le hs0 hab)

lemma self_le_leftLim (hf : Monotone f) {t t' : ℝ} (h : t < t') : f t ≤ leftLim f t' :=
  le_leftLim hf h

lemma lt_leftLim_iff (hf : Monotone f) (t : ℝ) (k : ℕ) :
    k < leftLim f t ↔ ∃ s < t, k < f s := by
  constructor
  · intro h
    obtain ⟨s0, hs0, he⟩ := leftLim_attained hf t
    exact ⟨s0, hs0, by rw [he s0 le_rfl hs0]; exact h⟩
  · rintro ⟨s, hs, hk⟩; exact lt_of_lt_of_le hk (le_leftLim hf hs)

lemma leftLim_eq_of_const (hf : Monotone f) {y t : ℝ} (hyt : y < t)
    (hc : ∀ s, y ≤ s → s < t → f s = f y) : leftLim f t = f y := by
  obtain ⟨s0, hs0, he⟩ := leftLim_attained hf t
  have h1 := he (max s0 y) (le_max_left _ _) (max_lt hs0 hyt)
  rw [← h1, hc _ (le_max_right _ _) (max_lt hs0 hyt)]

/-- Epochs of a path in (0, t]. -/
def epochSet (f : ℝ → ℕ) (t : ℝ) : Set ℝ := {τ | τ ∈ Ioc 0 t ∧ leftLim f τ < f τ}

lemma epochSet_finite (hf : Monotone f) (t : ℝ) : (epochSet f t).Finite := by
  apply Set.Finite.of_finite_image (f := f)
  · apply (Set.finite_Iic (f t)).subset
    rintro _ ⟨τ, hτ, rfl⟩; exact hf hτ.1.2
  · intro a ha b hb hab
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · have := le_leftLim hf h; have := hb.2; omega
    · have := le_leftLim hf h; have := ha.2; omega

lemma exists_epoch (hf : RegPath f) {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) (hlt : f x < f y) :
    ∃ τ, x < τ ∧ τ ≤ y ∧ leftLim f τ ≤ f x ∧ f x < f τ := by
  set S := {z | f x + 1 ≤ f z} with hS
  have hyS : y ∈ S := hlt
  have hbdd : BddBelow S := ⟨x, fun z hz => by
    by_contra h; push Not at h; have := hf.1 h.le; simp only [hS, mem_ofPred_eq] at hz; omega⟩
  set τ := sInf S with hτ
  have hτy : τ ≤ y := csInf_le hbdd hyS
  have hxτ : x ≤ τ := le_csInf ⟨y, hyS⟩ (fun z hz => by
    by_contra h; push Not at h; have := hf.1 h.le; simp only [hS, mem_ofPred_eq] at hz; omega)
  have hτS : f x + 1 ≤ f τ := by
    obtain ⟨δ, hδ, hc⟩ := hf.2 τ
    obtain ⟨z, hz, hzl⟩ := exists_lt_of_csInf_lt ⟨y, hyS⟩ (show sInf S < τ + δ by linarith)
    have hτz : τ ≤ z := csInf_le hbdd hz
    rw [← hc z hτz hzl]; exact hz
  have hxne : x < τ := lt_of_le_of_ne hxτ (fun h => by rw [← h] at hτS; omega)
  refine ⟨τ, hxne, hτy, ?_, by omega⟩
  apply csSup_le ((nonempty_Iio).image _)
  rintro _ ⟨s, hs, rfl⟩
  by_contra h; push Not at h
  have : τ ≤ s := csInf_le hbdd (show s ∈ S from h)
  linarith [show s < τ from hs]

lemma const_of_noEpoch (hf : RegPath f) {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y)
    (hno : ∀ τ, x < τ → τ ≤ y → ¬ leftLim f τ < f τ) : f y = f x := by
  by_contra hne
  have hlt : f x < f y := lt_of_le_of_ne (hf.1 hxy) (Ne.symm hne)
  obtain ⟨τ, h1, h2, h3, h4⟩ := exists_epoch hf hx hxy hlt
  exact hno τ h1 h2 (by omega)

/-- Arrival time of the k-th unit of the path. -/
noncomputable def arrT (f : ℝ → ℕ) (k : ℕ) : ℝ := sInf {s | k ≤ f s}

lemma arrT_spec (hf : RegPath f) (h0 : ∀ s, s ≤ 0 → f s = 0) {k : ℕ} (hk : 1 ≤ k) {t : ℝ}
    (hkt : k ≤ f t) (s : ℝ) : k ≤ f s ↔ arrT f k ≤ s := by
  have hbdd : BddBelow {s | k ≤ f s} := ⟨0, fun z hz => by
    by_contra h; push Not at h; have := h0 z h.le; simp only [mem_ofPred_eq] at hz; omega⟩
  have hmem : k ≤ f (arrT f k) := by
    obtain ⟨δ, hδ, hc⟩ := hf.2 (arrT f k)
    obtain ⟨z, hz, hzl⟩ := exists_lt_of_csInf_lt ⟨t, hkt⟩ (show sInf {s | k ≤ f s} < arrT f k + δ by
      unfold arrT; linarith)
    have : arrT f k ≤ z := csInf_le hbdd hz
    rw [← hc z this hzl]; exact hz
  constructor
  · intro h; exact csInf_le hbdd h
  · intro h; exact le_trans hmem (hf.1 h)

lemma arrT_pos (hf : RegPath f) (h0 : ∀ s, s ≤ 0 → f s = 0) {k : ℕ} (hk : 1 ≤ k) {t : ℝ}
    (hkt : k ≤ f t) : 0 < arrT f k := by
  by_contra h; push Not at h
  have := (arrT_spec hf h0 hk hkt (arrT f k)).mpr le_rfl
  rw [h0 _ h] at this; omega

lemma arrT_le (hf : RegPath f) (h0 : ∀ s, s ≤ 0 → f s = 0) {k : ℕ} (hk : 1 ≤ k) {t : ℝ}
    (hkt : k ≤ f t) : arrT f k ≤ t := (arrT_spec hf h0 hk hkt t).mp hkt

lemma arrT_eq_epoch (hf : RegPath f) (h0 : ∀ s, s ≤ 0 → f s = 0) {τ : ℝ} {k : ℕ}
    (hk1 : leftLim f τ < k) (hk2 : k ≤ f τ) : arrT f k = τ := by
  have hk : 1 ≤ k := by omega
  apply le_antisymm ((arrT_spec hf h0 hk hk2 τ).mp hk2)
  by_contra h; push Not at h
  have := le_leftLim hf.1 h
  have := (arrT_spec hf h0 hk hk2 (arrT f k)).mpr le_rfl
  omega

end paths

/-- The served-count recursion over customers: customer k+1 is served iff fewer units
have been served than were available before its arrival. -/
def srec (av : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | k + 1 => srec av k + if srec av k < av (k + 1) then 1 else 0

lemma srec_iter (av : ℕ → ℕ) (n0 : ℕ) (c : ℕ) :
    ∀ d, (∀ k, n0 < k → k ≤ n0 + d → av k = c) →
      srec av (n0 + d) = srec av n0 + min d (c - srec av n0) := by
  intro d
  induction d with
  | zero => intro _; simp
  | succ d ih =>
    intro hc
    have ih' := ih (fun k h1 h2 => hc k h1 (by omega))
    rw [show n0 + (d + 1) = (n0 + d) + 1 by omega, srec, ih', hc (n0 + d + 1) (by omega) le_rfl]
    split_ifs with h <;> omega

lemma srec_le (av : ℕ → ℕ) (k : ℕ) : srec av k ≤ k := by
  induction k with
  | zero => simp [srec]
  | succ k ih => simp only [srec]; split_ifs <;> omega

lemma srec_mono (av : ℕ → ℕ) : Monotone (srec av) :=
  monotone_nat_of_le_succ (fun k => by simp only [srec]; split_ifs <;> omega)

end LostSalesRQ

namespace LostSalesRQ

open MeasureTheory ProbabilityTheory Filter Set Topology

noncomputable def servStep (L : ℝ) (init U N : ℝ → ℕ) (acc : ℕ) (τ : ℝ) : ℕ :=
  acc + min (N τ - leftLim N τ) (leftLim init τ + leftLim U (τ - L) - acc)

lemma servedPath_eq (L : ℝ) (init U N : ℝ → ℕ) (hN : Monotone N) (t : ℝ) :
    servedPath L init U N t =
      ((epochSet_finite hN t).toFinset.sort (· ≤ ·)).foldl (servStep L init U N) 0 := by
  unfold servedPath
  have hE : ({τ | τ ∈ Ioc 0 t ∧ leftLim N τ < N τ} : Set ℝ).Finite := epochSet_finite hN t
  simp only [dif_pos hE]
  rfl

lemma sort_insert_max (s : Finset ℝ) (a : ℝ) (h : ∀ x ∈ s, x < a) :
    (insert a s).sort (· ≤ ·) = s.sort (· ≤ ·) ++ [a] := by
  apply List.Pairwise.eq_of_mem_iff (r := (· < ·))
  · exact (Finset.sortedLT_sort _).pairwise
  · rw [List.pairwise_append]
    refine ⟨(Finset.sortedLT_sort _).pairwise, List.pairwise_singleton _ _, ?_⟩
    intro x hx y hy
    rw [Finset.mem_sort] at hx
    rw [List.mem_singleton] at hy
    rw [hy]; exact h x hx
  · intro x
    simp only [Finset.mem_sort, Finset.mem_insert, List.mem_append, List.mem_singleton]
    tauto

/-- The customer availability: units available just before the k-th demand. -/
noncomputable def custAvail (L : ℝ) (init U N : ℝ → ℕ) (k : ℕ) : ℕ :=
  leftLim init (arrT N k) + leftLim U (arrT N k - L)

theorem servedPath_srec (L : ℝ) (init U N : ℝ → ℕ) (hN : RegPath N)
    (h0 : ∀ s, s ≤ 0 → N s = 0) (t : ℝ) :
    servedPath L init U N t = srec (custAvail L init U N) (N t) := by
  classical
  rw [servedPath_eq L init U N hN.1 t]
  set av := custAvail L init U N with hav
  suffices H : ∀ s : Finset ℝ, ∀ x : ℝ, (∀ τ, τ ∈ s ↔ τ ∈ epochSet N x) →
      (s.sort (· ≤ ·)).foldl (servStep L init U N) 0 = srec av (N x) by
    apply H
    intro τ; exact (epochSet_finite hN.1 t).mem_toFinset
  intro s
  induction s using Finset.induction_on_max with
  | empty =>
    intro x hx
    simp only [Finset.sort_empty, List.foldl_nil]
    rcases le_or_gt x 0 with h | h
    · rw [h0 x h]; rfl
    · rw [const_of_noEpoch hN le_rfl h.le (fun τ h1 h2 h3 => by
        have := (hx τ).mpr ⟨⟨h1, h2⟩, h3⟩; simp at this), h0 0 le_rfl]; rfl
  | insert a s hlt ih =>
    intro x hx
    have ha : a ∈ epochSet N x := (hx a).mp (Finset.mem_insert_self a s)
    have ha0 : 0 < a := ha.1.1
    set y : ℝ := if hs : s.Nonempty then s.max' hs else 0 with hy
    have hy0 : 0 ≤ y := by
      rw [hy]; split_ifs with hs
      · exact le_of_lt ((hx _).mp (Finset.mem_insert_of_mem (s.max'_mem hs))).1.1
      · exact le_rfl
    have hya : y < a := by
      rw [hy]; split_ifs with hs
      · exact hlt _ (s.max'_mem hs)
      · exact ha0
    have hsy : ∀ τ, τ ∈ s ↔ τ ∈ epochSet N y := by
      intro τ
      constructor
      · intro hτ
        have hτx := (hx τ).mp (Finset.mem_insert_of_mem hτ)
        refine ⟨⟨hτx.1.1, ?_⟩, hτx.2⟩
        rw [hy, dif_pos ⟨τ, hτ⟩]; exact s.le_max' τ hτ
      · intro hτ
        have hτa : τ < a := lt_of_le_of_lt hτ.1.2 hya
        have : τ ∈ insert a s := (hx τ).mpr ⟨⟨hτ.1.1, le_trans hτa.le ha.1.2⟩, hτ.2⟩
        rcases Finset.mem_insert.mp this with h | h
        · exact absurd h (ne_of_lt hτa)
        · exact h
    have hnoya : ∀ τ, y < τ → τ < a → ¬ leftLim N τ < N τ := by
      intro τ h1 h2 h3
      have : τ ∈ insert a s := (hx τ).mpr ⟨⟨lt_of_le_of_lt hy0 h1, le_trans h2.le ha.1.2⟩, h3⟩
      rcases Finset.mem_insert.mp this with h | h
      · exact absurd h (ne_of_lt h2)
      · have := (hsy τ).mp h; linarith [this.1.2]
    have hnoax : ∀ τ, a < τ → τ ≤ x → ¬ leftLim N τ < N τ := by
      intro τ h1 h2 h3
      have : τ ∈ insert a s := (hx τ).mpr ⟨⟨lt_trans ha0 h1, h2⟩, h3⟩
      rcases Finset.mem_insert.mp this with h | h
      · exact absurd h (ne_of_gt h1)
      · exact absurd (hlt τ h) (not_lt.mpr h1.le)
    have hconst : ∀ z, y ≤ z → z < a → N z = N y := fun z h1 h2 =>
      const_of_noEpoch hN hy0 h1 (fun τ t1 t2 => hnoya τ t1 (lt_of_le_of_lt t2 h2))
    have hll : leftLim N a = N y := leftLim_eq_of_const hN.1 hya hconst
    have hNx : N x = N a := const_of_noEpoch hN ha0.le ha.1.2 hnoax
    rw [sort_insert_max s a hlt, List.foldl_append, ih y hsy, hNx]
    simp only [List.foldl_cons, List.foldl_nil]
    unfold servStep
    rw [hll]
    have hle : N y ≤ N a := by rw [← hll]; exact leftLim_le_self hN.1 a
    have hit := srec_iter av (N y) (leftLim init a + leftLim U (a - L)) (N a - N y) (by
      intro k hk1 hk2
      rw [hav]; unfold custAvail
      rw [arrT_eq_epoch hN h0 (by rw [hll]; exact hk1) (by omega)])
    rw [show N y + (N a - N y) = N a by omega] at hit
    rw [hit]

end LostSalesRQ

namespace LostSalesRQ

open MeasureTheory ProbabilityTheory Filter Set Topology

lemma pm_hasSum (t : ℝ) (ht : 0 ≤ t) : HasSum (fun n => poisMass t n) 1 := by
  have := hasSum_one_poissonMeasure ⟨t, ht⟩
  unfold poisMass
  exact this

lemma pm_mean_hasSum (t : ℝ) (ht : 0 ≤ t) : HasSum (fun n : ℕ => (n : ℝ) * poisMass t n) t := by
  have h1 : HasSum (fun n => pPrev n t) 1 := by
    rw [← hasSum_nat_add_iff' 1]
    simp only [Finset.range_one, Finset.sum_singleton, pPrev, sub_zero]
    simpa using pm_hasSum t ht
  have h2 := h1.mul_left t
  rw [mul_one] at h2
  refine h2.congr_fun ?_
  intro n; rw [pPrev_mul]

variable {lam : ℝ}

lemma DemandSpace.measurable_N (S : DemandSpace lam) (t : ℝ) : Measurable (S.N t) :=
  (S.N_adapted t).mono (S.𝓕.le t) le_rfl

lemma DemandSpace.regPath (S : DemandSpace lam) (ω : S.Ω) : RegPath (fun s => S.N s ω) :=
  ⟨S.N_mono ω, S.N_rcont ω⟩

/-- Increment of the demand count. -/
def DemandSpace.inc (S : DemandSpace lam) (s t : ℝ) (ω : S.Ω) : ℕ := S.N t ω - S.N s ω

lemma DemandSpace.measurable_inc (S : DemandSpace lam) (s t : ℝ) : Measurable (S.inc s t) := by
  unfold DemandSpace.inc
  exact (S.measurable_N t).sub (S.measurable_N s)

lemma DemandSpace.lintegral_inc (S : DemandSpace lam) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t)
    (hx : 0 ≤ lam * (t - s)) :
    ∫⁻ ω, (S.inc s t ω : ENNReal) ∂S.ν = ENNReal.ofReal (lam * (t - s)) := by
  have hm := S.measurable_inc s t
  rw [← lintegral_map (f := fun n : ℕ => (n : ENNReal)) (by fun_prop) hm, lintegral_countable']
  have hpt : ∀ n : ℕ, (n : ENNReal) * (S.ν.map (S.inc s t)) {n} =
      ENNReal.ofReal ((n : ℝ) * poisMass (lam * (t - s)) n) := by
    intro n
    rw [Measure.map_apply hm (measurableSet_singleton n)]
    have : S.inc s t ⁻¹' {n} = {ω | S.N t ω - S.N s ω = n} := rfl
    rw [this, S.N_law s t hs hst n, ENNReal.ofReal_mul (Nat.cast_nonneg n), ENNReal.ofReal_natCast]
  simp_rw [hpt]
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => mul_nonneg (Nat.cast_nonneg n)
    (by unfold poisMass; positivity)) (pm_mean_hasSum _ hx).summable, (pm_mean_hasSum _ hx).tsum_eq]

lemma DemandSpace.integrable_inc (S : DemandSpace lam) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t)
    (hx : 0 ≤ lam * (t - s)) : Integrable (fun ω => (S.inc s t ω : ℝ)) S.ν := by
  refine ⟨((measurable_from_nat (f := fun n : ℕ => (n : ℝ))).comp (S.measurable_inc s t)).aestronglyMeasurable, ?_⟩
  unfold HasFiniteIntegral
  have : ∀ ω, (‖(S.inc s t ω : ℝ)‖ₑ) = (S.inc s t ω : ENNReal) := fun ω => by
    rw [Real.enorm_natCast]
  simp_rw [this, S.lintegral_inc hs hst hx]
  exact ENNReal.ofReal_lt_top

lemma DemandSpace.integral_inc (S : DemandSpace lam) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t)
    (hx : 0 ≤ lam * (t - s)) : ∫ ω, (S.inc s t ω : ℝ) ∂S.ν = lam * (t - s) := by
  rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall (fun ω => Nat.cast_nonneg _))
    (((measurable_from_nat (f := fun n : ℕ => (n : ℝ))).comp (S.measurable_inc s t)).aestronglyMeasurable)]
  have : ∀ ω, ENNReal.ofReal (S.inc s t ω : ℝ) = (S.inc s t ω : ENNReal) := fun ω =>
    ENNReal.ofReal_natCast _
  simp_rw [this, S.lintegral_inc hs hst hx, ENNReal.toReal_ofReal hx]

lemma DemandSpace.integral_mul_inc (S : DemandSpace lam) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t)
    (hx : 0 ≤ lam * (t - s)) (Y : S.Ω → ℝ) (hY : Measurable[S.𝓕 s] Y) :
    ∫ ω, Y ω * (S.inc s t ω : ℝ) ∂S.ν = (∫ ω, Y ω ∂S.ν) * (lam * (t - s)) := by
  have hind : IndepFun Y (fun ω => (S.inc s t ω : ℝ)) S.ν := by
    rw [IndepFun_iff_Indep]
    have h0 := S.N_indep s t hs hst
    have h1 : MeasurableSpace.comap (fun ω => (S.inc s t ω : ℝ)) inferInstance ≤
        MeasurableSpace.comap (fun ω => S.N t ω - S.N s ω) inferInstance := by
      have : (fun ω => (S.inc s t ω : ℝ)) = (fun n : ℕ => (n : ℝ)) ∘ (fun ω => S.N t ω - S.N s ω) :=
        rfl
      rw [this, ← MeasurableSpace.comap_comp]
      exact MeasurableSpace.comap_mono (measurable_from_nat (f := fun n : ℕ => (n : ℝ))).comap_le
    exact (indep_of_indep_of_le_left (indep_of_indep_of_le_right h0 hY.comap_le) h1).symm
  have hYm : Measurable Y := hY.mono (S.𝓕.le s) le_rfl
  rw [show (fun ω => Y ω * (S.inc s t ω : ℝ)) = Y * (fun ω => (S.inc s t ω : ℝ)) from rfl,
    hind.integral_mul_eq_mul_integral hYm.aestronglyMeasurable
      (((measurable_from_nat (f := fun n : ℕ => (n : ℝ))).comp (S.measurable_inc s t)).aestronglyMeasurable),
    S.integral_inc hs hst hx]

lemma DemandSpace.prob_inc_ge_two (S : DemandSpace lam) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t)
    (hx : 0 ≤ lam * (t - s)) :
    S.ν {ω | 2 ≤ S.inc s t ω} ≤ ENNReal.ofReal ((lam * (t - s)) ^ 2) := by
  set x := lam * (t - s) with hxdef
  have hm := S.measurable_inc s t
  have hsplit : (univ : Set S.Ω) = {ω | 2 ≤ S.inc s t ω} ∪ ({ω | S.inc s t ω = 0} ∪
      {ω | S.inc s t ω = 1}) := by
    ext ω; simp only [mem_univ, mem_union, mem_ofPred_eq, true_iff]; omega
  have hdisj1 : Disjoint {ω | 2 ≤ S.inc s t ω} ({ω | S.inc s t ω = 0} ∪ {ω | S.inc s t ω = 1}) := by
    rw [Set.disjoint_left]; intro ω h1 h2
    simp only [mem_union, mem_ofPred_eq] at h1 h2; omega
  have hdisj2 : Disjoint {ω | S.inc s t ω = 0} {ω | S.inc s t ω = 1} := by
    rw [Set.disjoint_left]; intro ω h1 h2; simp only [mem_ofPred_eq] at h1 h2; omega
  have hmeas : ∀ n : ℕ, MeasurableSet {ω | S.inc s t ω = n} := fun n =>
    hm (measurableSet_singleton n)
  have h1 := measure_univ (μ := S.ν)
  rw [hsplit, measure_union hdisj1 ((hmeas 0).union (hmeas 1)), measure_union hdisj2 (hmeas 1)] at h1
  have e0 : S.ν {ω | S.inc s t ω = 0} = ENNReal.ofReal (poisMass x 0) := S.N_law s t hs hst 0
  have e1 : S.ν {ω | S.inc s t ω = 1} = ENNReal.ofReal (poisMass x 1) := S.N_law s t hs hst 1
  rw [e0, e1] at h1
  have hp0 : poisMass x 0 = Real.exp (-x) := by simp [poisMass]
  have hp1 : poisMass x 1 = Real.exp (-x) * x := by simp [poisMass]
  rw [hp0, hp1, ← ENNReal.ofReal_add (Real.exp_pos _).le (by positivity)] at h1
  have hfin : S.ν {ω | 2 ≤ S.inc s t ω} = 1 - ENNReal.ofReal (Real.exp (-x) + Real.exp (-x) * x) := by
    rw [← h1, ENNReal.add_sub_cancel_right ENNReal.ofReal_ne_top]
  rw [hfin, ← ENNReal.ofReal_one, ← ENNReal.ofReal_sub _ (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  have he : 1 - x ≤ Real.exp (-x) := by linarith [Real.add_one_le_exp (-x)]
  nlinarith [Real.exp_pos (-x)]

end LostSalesRQ

namespace LostSalesRQ

open MeasureTheory ProbabilityTheory Filter Set Topology

noncomputable def gstep (T : ℝ) (n : ℕ) : ℝ := T / (n + 1)
noncomputable def gidx (T : ℝ) (n : ℕ) (x : ℝ) : ℕ := ⌈x / gstep T n⌉₊ - 1
noncomputable def gpt (T : ℝ) (n : ℕ) (x : ℝ) : ℝ := (gidx T n x : ℝ) * gstep T n

section grid
variable {T : ℝ} (hT : 0 < T) (n : ℕ)
include hT

lemma gstep_pos : 0 < gstep T n := by unfold gstep; positivity

lemma gidx_eq_iff {x : ℝ} (hx : 0 < x) (j : ℕ) :
    gidx T n x = j ↔ (j : ℝ) * gstep T n < x ∧ x ≤ ((j : ℝ) + 1) * gstep T n := by
  have hδ := gstep_pos hT n
  have hc : 1 ≤ ⌈x / gstep T n⌉₊ := Nat.one_le_iff_ne_zero.mpr (by
    rw [Ne, Nat.ceil_eq_zero, not_le]; positivity)
  unfold gidx
  rw [show (⌈x / gstep T n⌉₊ - 1 = j) ↔ (⌈x / gstep T n⌉₊ = j + 1) by omega,
    Nat.ceil_eq_iff (by omega)]
  simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one]
  rw [lt_div_iff₀ hδ, div_le_iff₀ hδ]

lemma gpt_lt {x : ℝ} (hx : 0 < x) : gpt T n x < x := by
  have := (gidx_eq_iff hT n hx (gidx T n x)).mp rfl
  exact this.1

lemma le_gpt {x : ℝ} (hx : 0 < x) : x - gstep T n ≤ gpt T n x := by
  have := (gidx_eq_iff hT n hx (gidx T n x)).mp rfl
  unfold gpt; linarith [this.2]

lemma gidx_lt {x : ℝ} (hx : 0 < x) (hxT : x ≤ T) : gidx T n x < n + 1 := by
  have := (gidx_eq_iff hT n hx (gidx T n x)).mp rfl
  have h1 : (gidx T n x : ℝ) * gstep T n < T := lt_of_lt_of_le this.1 hxT
  have h2 : (gidx T n x : ℝ) < n + 1 := by
    unfold gstep at h1
    rw [mul_div_assoc', div_lt_iff₀ (by positivity)] at h1
    nlinarith
  exact_mod_cast h2

omit hT in
lemma gstep_tendsto : Tendsto (fun n => gstep T n) atTop (𝓝 0) := by
  unfold gstep
  have := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
  have h2 := this.const_mul T
  rw [mul_zero] at h2
  refine h2.congr (fun n => ?_)
  ring

lemma tendsto_gpt {x : ℝ} (hx : 0 < x) : Tendsto (fun n => gpt T n x) atTop (𝓝[<] x) := by
  apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
  · have h1 : Tendsto (fun n => x - gstep T n) atTop (𝓝 x) := by
      have := (tendsto_const_nhds (x := x)).sub (gstep_tendsto (T := T))
      rwa [sub_zero] at this
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le h1 tendsto_const_nhds
      (fun n => le_gpt hT n hx) (fun n => (gpt_lt hT n hx).le)
  · exact Eventually.of_forall (fun n => gpt_lt hT n hx)

lemma gstep_mul_succ : ((n : ℝ) + 1) * gstep T n = T := by
  unfold gstep; field_simp

end grid

lemma measurable_gidx (T : ℝ) (n : ℕ) : Measurable (gidx T n) := by
  unfold gidx
  exact (measurable_from_nat (f := fun m : ℕ => m - 1)).comp
    ((measurable_id.div_const _).nat_ceil)

lemma intervalIntegrable_of_bdd {f : ℝ → ℝ} (hf : Measurable f) {C : ℝ} (hb : ∀ x, |f x| ≤ C)
    (a b : ℝ) : IntervalIntegrable f volume a b := by
  rw [intervalIntegrable_iff]
  exact Measure.integrableOn_of_bounded (M := C) (by simp) hf.aestronglyMeasurable
    (Eventually.of_forall (fun x => by rw [Real.norm_eq_abs]; exact hb x))

/-- Poisson compensation: for a bounded adapted process with left limits, the expected sum over
demands of its left limits equals its expected time integral. -/
theorem compensation (S : DemandSpace 1) (T : ℝ) (hT : 0 < T) (H : ℝ → S.Ω → ℝ) (C : ℝ)
    (hHm : ∀ t, 0 ≤ t → Measurable[S.𝓕 t] (H t))
    (hHb : ∀ t ω, |H t ω| ≤ C)
    (Hl : ℕ → S.Ω → ℝ)
    (hHl : ∀ ω k, 1 ≤ k → k ≤ S.N T ω →
      Tendsto (fun s => H s ω) (𝓝[<] (arrT (fun s => S.N s ω) k)) (𝓝 (Hl k ω)))
    (hHae : ∀ ω, ∀ᵐ t ∂volume, t ∈ Ioc 0 T → Tendsto (fun s => H s ω) (𝓝[<] t) (𝓝 (H t ω))) :
    Integrable (fun ω => ∑ k ∈ Finset.Icc 1 (S.N T ω), Hl k ω) S.ν ∧
    Integrable (fun ω => ∫ t in (0:ℝ)..T, H t ω) S.ν ∧
    ∫ ω, ∑ k ∈ Finset.Icc 1 (S.N T ω), Hl k ω ∂S.ν = ∫ ω, (∫ t in (0:ℝ)..T, H t ω) ∂S.ν := by
  have hHm' : ∀ t, 0 ≤ t → Measurable (H t) := fun t ht => (hHm t ht).mono (S.𝓕.le t) le_rfl
  -- the Riemann-type sums
  set Q : ℕ → S.Ω → ℝ := fun n ω => ∑ j ∈ Finset.range (n + 1),
    H (j * gstep T n) ω * (S.inc (j * gstep T n) ((j + 1) * gstep T n) ω : ℝ) with hQ
  set R : ℕ → S.Ω → ℝ := fun n ω => ∑ j ∈ Finset.range (n + 1), H (j * gstep T n) ω * gstep T n with hR
  have hjδ : ∀ n (j : ℕ), 0 ≤ (j : ℝ) * gstep T n := fun n j =>
    mul_nonneg (Nat.cast_nonneg j) (gstep_pos hT n).le
  have hinc_int : ∀ n (j : ℕ), Integrable (fun ω => (S.inc (j * gstep T n) ((j + 1) * gstep T n) ω : ℝ)) S.ν :=
    fun n j => S.integrable_inc (hjδ n j) (by nlinarith [gstep_pos hT n]) (by
      nlinarith [gstep_pos hT n])
  have hQm : ∀ n, Measurable (Q n) := fun n => Finset.measurable_sum _ (fun j _ =>
    (hHm' _ (hjδ n j)).mul ((measurable_from_nat (f := fun m : ℕ => (m : ℝ))).comp
      (S.measurable_inc _ _)))
  have hRm : ∀ n, Measurable (R n) := fun n => Finset.measurable_sum _ (fun j _ =>
    (hHm' _ (hjδ n j)).mul_const _)
  -- expectations agree
  have hQR : ∀ n, ∫ ω, Q n ω ∂S.ν = ∫ ω, R n ω ∂S.ν := by
    intro n
    rw [integral_finsetSum _ (fun j _ => (hinc_int n j).bdd_mul
      (hHm' _ (hjδ n j)).aestronglyMeasurable (Eventually.of_forall (fun ω => by
        rw [Real.norm_eq_abs]; exact hHb _ ω))),
      integral_finsetSum _ (fun j _ => (Integrable.of_bound (C := C)
        (hHm' _ (hjδ n j)).aestronglyMeasurable (Eventually.of_forall (fun ω => by
          rw [Real.norm_eq_abs]; exact hHb _ ω))).mul_const _)]
    apply Finset.sum_congr rfl
    intro j _
    rw [S.integral_mul_inc (hjδ n j) (by nlinarith [gstep_pos hT n]) (by nlinarith [gstep_pos hT n])
      _ (hHm _ (hjδ n j)), integral_mul_const]
    ring
  -- pathwise identity for Q
  have hQpath : ∀ n ω, Q n ω = ∑ k ∈ Finset.Icc 1 (S.N T ω),
      H (gpt T n (arrT (fun s => S.N s ω) k)) ω := by
    intro n ω
    set f : ℝ → ℕ := fun s => S.N s ω with hf
    have hreg : RegPath f := S.regPath ω
    have h0 : ∀ s, s ≤ 0 → f s = 0 := fun s hs => S.N_nonpos ω s hs
    have hσpos : ∀ k ∈ Finset.Icc 1 (f T), 0 < arrT f k := fun k hk =>
      arrT_pos hreg h0 (Finset.mem_Icc.mp hk).1 (Finset.mem_Icc.mp hk).2
    have hmaps : ∀ k ∈ Finset.Icc 1 (f T), gidx T n (arrT f k) ∈ Finset.range (n + 1) := by
      intro k hk
      exact Finset.mem_range.mpr (gidx_lt hT n (hσpos k hk)
        (arrT_le hreg h0 (Finset.mem_Icc.mp hk).1 (Finset.mem_Icc.mp hk).2))
    rw [← Finset.sum_fiberwise_of_maps_to hmaps]
    apply Finset.sum_congr rfl
    intro j hj
    have hjn : j ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    have hj1T : ((j : ℝ) + 1) * gstep T n ≤ T := by
      have h1 := gstep_mul_succ hT n
      have h2 : (j : ℝ) + 1 ≤ n + 1 := by exact_mod_cast Nat.succ_le_succ hjn
      nlinarith [gstep_pos hT n]
    have hfib : (Finset.Icc 1 (f T)).filter (fun k => gidx T n (arrT f k) = j) =
        Finset.Ioc (f (j * gstep T n)) (f ((j + 1) * gstep T n)) := by
      ext k
      simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_Ioc]
      constructor
      · rintro ⟨⟨hk1, hkT⟩, hg⟩
        have hσ := (gidx_eq_iff hT n (arrT_pos hreg h0 hk1 hkT) j).mp hg
        refine ⟨?_, (arrT_spec hreg h0 hk1 hkT _).mpr hσ.2⟩
        by_contra hc; push Not at hc
        have := (arrT_spec hreg h0 hk1 hkT _).mp hc
        linarith [hσ.1]
      · rintro ⟨hk1, hk2⟩
        have hk1' : 1 ≤ k := by omega
        have hkT : k ≤ f T := le_trans hk2 (hreg.1 hj1T)
        refine ⟨⟨hk1', hkT⟩, ?_⟩
        rw [gidx_eq_iff hT n (arrT_pos hreg h0 hk1' hkT)]
        constructor
        · by_contra hc; push Not at hc
          have := (arrT_spec hreg h0 hk1' hkT _).mpr hc
          omega
        · exact (arrT_spec hreg h0 hk1' hkT _).mp hk2
    have hval : ∀ k ∈ (Finset.Icc 1 (f T)).filter (fun k => gidx T n (arrT f k) = j),
        H (gpt T n (arrT f k)) ω = H (j * gstep T n) ω := by
      intro k hk
      rw [Finset.mem_filter] at hk
      unfold gpt; rw [hk.2]
    rw [Finset.sum_congr rfl hval, Finset.sum_const, hfib, Nat.card_Ioc, nsmul_eq_mul, mul_comm]
    rfl
  -- pathwise identity for R
  have hRpath : ∀ n ω, R n ω = ∫ t in (0:ℝ)..T, H (gpt T n t) ω := by
    intro n ω
    have hmeasF : Measurable (fun t => H (gpt T n t) ω) := by
      have : (fun t => H (gpt T n t) ω) = (fun m : ℕ => H ((m : ℝ) * gstep T n) ω) ∘ gidx T n := rfl
      rw [this]; exact (measurable_from_nat).comp (measurable_gidx T n)
    have hint : ∀ j < n + 1, IntervalIntegrable (fun t => H (gpt T n t) ω) volume
        ((j : ℝ) * gstep T n) (((j + 1 : ℕ) : ℝ) * gstep T n) := fun j _ =>
      intervalIntegrable_of_bdd hmeasF (fun x => hHb _ ω) _ _
    have hsum := intervalIntegral.sum_integral_adjacent_intervals (a := fun j : ℕ => (j : ℝ) * gstep T n)
      (f := fun t => H (gpt T n t) ω) (μ := volume) hint
    simp only [Nat.cast_zero, zero_mul] at hsum
    rw [show ((n + 1 : ℕ) : ℝ) * gstep T n = T by push_cast; exact gstep_mul_succ hT n] at hsum
    rw [← hsum]
    apply Finset.sum_congr rfl
    intro j _
    have hle : (j : ℝ) * gstep T n ≤ ((j + 1 : ℕ) : ℝ) * gstep T n := by
      push_cast; nlinarith [gstep_pos hT n]
    rw [intervalIntegral.integral_congr_ae (g := fun _ => H (j * gstep T n) ω) ?_,
      intervalIntegral.integral_const, smul_eq_mul]
    · push_cast; ring
    · refine Eventually.of_forall (fun t ht => ?_)
      rw [uIoc_of_le hle] at ht
      have htpos : 0 < t := lt_of_le_of_lt (hjδ n j) ht.1
      have : gidx T n t = j := (gidx_eq_iff hT n htpos j).mpr ⟨ht.1, by push_cast at ht; exact ht.2⟩
      unfold gpt; rw [this]
  -- limits
  have hQlim : ∀ ω, Tendsto (fun n => Q n ω) atTop
      (𝓝 (∑ k ∈ Finset.Icc 1 (S.N T ω), Hl k ω)) := by
    intro ω
    simp_rw [hQpath _ ω]
    apply tendsto_finsetSum
    intro k hk
    have hk1 := (Finset.mem_Icc.mp hk).1
    have hkT := (Finset.mem_Icc.mp hk).2
    exact (hHl ω k hk1 hkT).comp (tendsto_gpt hT (arrT_pos (S.regPath ω)
      (fun s hs => S.N_nonpos ω s hs) hk1 hkT))
  have hRlim : ∀ ω, Tendsto (fun n => R n ω) atTop (𝓝 (∫ t in (0:ℝ)..T, H t ω)) := by
    intro ω
    simp_rw [hRpath _ ω]
    apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence (fun _ => C)
    · refine Eventually.of_forall (fun n => ?_)
      have : (fun t => H (gpt T n t) ω) = (fun m : ℕ => H ((m : ℝ) * gstep T n) ω) ∘ gidx T n := rfl
      rw [this]; exact ((measurable_from_nat).comp (measurable_gidx T n)).aestronglyMeasurable
    · exact Eventually.of_forall (fun n => Eventually.of_forall (fun x _ => by
        rw [Real.norm_eq_abs]; exact hHb _ ω))
    · exact intervalIntegrable_const
    · filter_upwards [hHae ω] with t ht hmem
      rw [uIoc_of_le hT.le] at hmem
      exact (ht hmem).comp (tendsto_gpt hT hmem.1)
  have hLm1 : Measurable (fun ω => ∑ k ∈ Finset.Icc 1 (S.N T ω), Hl k ω) :=
    measurable_of_tendsto_metrizable hQm (tendsto_pi_nhds.mpr hQlim)
  have hLm2 : Measurable (fun ω => ∫ t in (0:ℝ)..T, H t ω) :=
    measurable_of_tendsto_metrizable hRm (tendsto_pi_nhds.mpr hRlim)
  -- bounds
  have hNint : Integrable (fun ω => C * (S.N T ω : ℝ)) S.ν := by
    have := (S.integrable_inc le_rfl hT.le (by linarith)).const_mul C
    refine this.congr (Eventually.of_forall (fun ω => ?_))
    simp only [DemandSpace.inc, S.N_nonpos ω 0 le_rfl, Nat.sub_zero]
  have hQb : ∀ n ω, ‖Q n ω‖ ≤ C * (S.N T ω : ℝ) := by
    intro n ω
    rw [Real.norm_eq_abs]
    have htel : ∑ j ∈ Finset.range (n + 1), (S.inc (j * gstep T n) ((j + 1) * gstep T n) ω : ℝ) =
        (S.N T ω : ℝ) := by
      have hmono : ∀ j : ℕ, S.N (j * gstep T n) ω ≤ S.N ((j + 1) * gstep T n) ω := fun j =>
        S.N_mono ω (by nlinarith [gstep_pos hT n])
      have := Finset.sum_range_sub (fun j : ℕ => (S.N (j * gstep T n) ω : ℝ)) (n + 1)
      have e1 : ((n + 1 : ℕ) : ℝ) * gstep T n = T := by push_cast; exact gstep_mul_succ hT n
      simp only [e1, Nat.cast_zero, zero_mul, S.N_nonpos ω 0 le_rfl, sub_zero] at this
      rw [← this]
      apply Finset.sum_congr rfl
      intro j _
      unfold DemandSpace.inc
      rw [Nat.cast_sub (hmono j)]
      push_cast; ring_nf
    rw [← htel, Finset.mul_sum]
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum (fun j _ => ?_))
    rw [abs_mul, Nat.abs_cast]
    exact mul_le_mul_of_nonneg_right (hHb _ ω) (Nat.cast_nonneg _)
  have hRb : ∀ n ω, ‖R n ω‖ ≤ C * T := by
    intro n ω
    rw [Real.norm_eq_abs]
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    calc ∑ j ∈ Finset.range (n + 1), |H (j * gstep T n) ω * gstep T n|
        ≤ ∑ j ∈ Finset.range (n + 1), C * gstep T n := Finset.sum_le_sum (fun j _ => by
          rw [abs_mul, abs_of_pos (gstep_pos hT n)]
          exact mul_le_mul_of_nonneg_right (hHb _ ω) (gstep_pos hT n).le)
      _ = C * T := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          have h1 := gstep_mul_succ hT n
          push_cast; linear_combination C * h1
  have hlim1 := tendsto_integral_of_dominated_convergence _ (fun n => (hQm n).aestronglyMeasurable)
    hNint (fun n => Eventually.of_forall (hQb n)) (Eventually.of_forall hQlim)
  have hlim2 := tendsto_integral_of_dominated_convergence _ (fun n => (hRm n).aestronglyMeasurable)
    (integrable_const (μ := S.ν) (C * T)) (fun n => Eventually.of_forall (hRb n)) (Eventually.of_forall hRlim)
  refine ⟨?_, ?_, ?_⟩
  · refine hNint.mono' hLm1.aestronglyMeasurable (Eventually.of_forall (fun ω => ?_))
    exact le_of_tendsto' ((continuous_norm.tendsto _).comp (hQlim ω)) (fun n => hQb n ω)
  · refine (integrable_const (μ := S.ν) (C * T)).mono' hLm2.aestronglyMeasurable
      (Eventually.of_forall (fun ω => ?_))
    exact le_of_tendsto' ((continuous_norm.tendsto _).comp (hRlim ω)) (fun n => hRb n ω)
  · simp_rw [hQR] at hlim1
    exact tendsto_nhds_unique hlim1 hlim2

end LostSalesRQ

namespace LostSalesRQ

open MeasureTheory ProbabilityTheory Filter Set Topology

/-- No two demands arrive at the same epoch, almost surely. -/
lemma ae_noBatch (S : DemandSpace 1) (T : ℝ) (hT : 0 < T) :
    ∀ᵐ ω ∂S.ν, ∀ τ, 0 < τ → τ ≤ T → S.N τ ω ≤ leftLim (fun s => S.N s ω) τ + 1 := by
  rw [ae_iff]
  set B : ℕ → Set S.Ω := fun n => ⋃ j ∈ Finset.range (n + 1),
    {ω | 2 ≤ S.inc (j * gstep T n) ((j + 1) * gstep T n) ω} with hB
  have hBm : ∀ n, MeasurableSet (B n) := fun n =>
    Finset.measurableSet_biUnion _ (fun j _ => S.measurable_inc _ _ measurableSet_Ici)
  have hsub : {ω | ¬ ∀ τ, 0 < τ → τ ≤ T → S.N τ ω ≤ leftLim (fun s => S.N s ω) τ + 1} ⊆
      ⋂ n, B n := by
    intro ω hω
    simp only [mem_ofPred_eq, not_forall, not_le] at hω
    obtain ⟨τ, hτ0, hτT, hjump⟩ := hω
    simp only [mem_iInter]
    intro n
    have hj := gidx_lt hT n hτ0 hτT
    have hg := (gidx_eq_iff hT n hτ0 (gidx T n τ)).mp rfl
    simp only [hB, mem_iUnion, Finset.mem_range, exists_prop, mem_ofPred_eq]
    refine ⟨gidx T n τ, hj, ?_⟩
    unfold DemandSpace.inc
    have h1 : S.N (gidx T n τ * gstep T n) ω ≤ leftLim (fun s => S.N s ω) τ :=
      le_leftLim (S.N_mono ω) hg.1
    have h2 : S.N τ ω ≤ S.N ((gidx T n τ + 1) * gstep T n) ω := S.N_mono ω hg.2
    omega
  apply measure_mono_null hsub
  have hb : ∀ n : ℕ, S.ν (⋂ n, B n) ≤ ENNReal.ofReal (T ^ 2 * (1 / ((n : ℝ) + 1))) := by
    intro n
    calc S.ν (⋂ n, B n) ≤ S.ν (B n) := measure_mono (iInter_subset _ n)
      _ ≤ ∑ j ∈ Finset.range (n + 1), S.ν {ω | 2 ≤ S.inc (j * gstep T n) ((j + 1) * gstep T n) ω} :=
          measure_biUnion_finset_le _ _
      _ ≤ ∑ j ∈ Finset.range (n + 1), ENNReal.ofReal ((gstep T n) ^ 2) := by
          apply Finset.sum_le_sum; intro j _
          have hpos := gstep_pos hT n
          have := S.prob_inc_ge_two (s := j * gstep T n) (t := (j + 1) * gstep T n)
            (by positivity) (by nlinarith) (by nlinarith)
          refine le_trans this (le_of_eq ?_)
          congr 1; ring
      _ = ENNReal.ofReal (T ^ 2 * (1 / ((n : ℝ) + 1))) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
            ← ENNReal.ofReal_mul (by positivity)]
          congr 1; unfold gstep; push_cast; field_simp
  have ht : Tendsto (fun n : ℕ => ENNReal.ofReal (T ^ 2 * (1 / ((n : ℝ) + 1)))) atTop (𝓝 0) := by
    rw [← ENNReal.ofReal_zero]
    apply ENNReal.tendsto_ofReal
    have := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (T ^ 2)
    rwa [mul_zero] at this
  exact le_antisymm (ge_of_tendsto' ht hb) zero_le

end LostSalesRQ

namespace LostSalesRQ

open MeasureTheory ProbabilityTheory Filter Set Topology

noncomputable def cdfPrev (i : ℕ) (τ : ℝ) : ℝ := ∑ n ∈ Finset.range i, poisMass τ n

/-- Value of a unit of rank i with remaining delivery time τ. -/
noncomputable def VV (η g : ℝ) (i : ℕ) (τ : ℝ) : ℝ :=
  expectedShortfall τ i + η * poisTail τ i - g

/-- Its derivative in τ. -/
noncomputable def dVV (η : ℝ) (i : ℕ) (τ : ℝ) : ℝ := η * pPrev i τ - cdfPrev i τ

lemma hasDerivAt_VV (η g : ℝ) (i : ℕ) (τ : ℝ) : HasDerivAt (VV η g i) (dVV η i τ) τ := by
  unfold VV dVV
  have key : ∀ i : ℕ, HasDerivAt (fun τ => expectedShortfall τ i + η * poisTail τ i)
      (η * pPrev i τ - cdfPrev i τ) τ := by
    intro i
    induction i with
    | zero =>
      have : (fun τ => expectedShortfall τ 0 + η * poisTail τ 0) = fun _ => η := by
        funext τ; simp [expectedShortfall, poisTail]
      rw [this]
      simp only [pPrev, cdfPrev, Finset.range_zero, Finset.sum_empty, mul_zero, sub_zero]
      exact hasDerivAt_const τ η
    | succ i ih =>
      have hG : (fun τ => expectedShortfall τ (i + 1) + η * poisTail τ (i + 1)) =
          fun τ => (expectedShortfall τ i + η * poisTail τ i) + poisCdf τ i - η * poisMass τ i := by
        funext τ
        have hG : expectedShortfall τ (i + 1) = expectedShortfall τ i + poisCdf τ i := by
          unfold expectedShortfall poisCdf
          rw [Finset.sum_range_succ _ (i + 1)]
          push_cast
          simp only [sub_self, zero_mul, add_zero]
          rw [← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl; intro j _; ring
        have hP : poisTail τ (i + 1) = poisTail τ i - poisMass τ i := by
          unfold poisTail; rw [Finset.sum_range_succ]; ring
        rw [hG, hP]; ring
      rw [hG]
      have h := (ih.add (hasDerivAt_pc i τ)).sub ((hasDerivAt_pm i τ).const_mul η)
      refine h.congr_deriv ?_
      simp only [pPrev, cdfPrev, Finset.sum_range_succ, poisCdf]
      ring
  exact (key i).sub_const g

lemma continuous_VV (η g : ℝ) (i : ℕ) : Continuous (VV η g i) :=
  continuous_iff_continuousAt.mpr (fun τ => (hasDerivAt_VV η g i τ).continuousAt)

lemma continuous_dVV (η : ℝ) (i : ℕ) : Continuous (dVV η i) := by
  unfold dVV cdfPrev
  have := continuous_pPrev i
  have h2 : Continuous (fun τ => ∑ n ∈ Finset.range i, poisMass τ n) :=
    continuous_finsetSum _ (fun n _ => continuous_pm n)
  fun_prop

lemma VV_zero (η g : ℝ) {i : ℕ} (hi : 1 ≤ i) : VV η g i 0 = i - g := by
  unfold VV expectedShortfall poisTail
  have hpm : ∀ n : ℕ, poisMass 0 n = if n = 0 then 1 else 0 := by
    intro n; unfold poisMass; cases n <;> simp
  simp only [hpm, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_range]
  rw [if_pos (by omega), if_pos (by omega)]
  simp

lemma VV_sub_succ (η g : ℝ) (i : ℕ) (τ : ℝ) : VV η g i τ - VV η g (i + 1) τ = dVV η (i + 1) τ := by
  unfold VV dVV cdfPrev pPrev
  have hG : expectedShortfall τ (i + 1) = expectedShortfall τ i + poisCdf τ i := by
    unfold expectedShortfall poisCdf
    rw [Finset.sum_range_succ _ (i + 1)]
    push_cast
    simp only [sub_self, zero_mul, add_zero]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro j _; ring
  have hP : poisTail τ (i + 1) = poisTail τ i - poisMass τ i := by
    unfold poisTail; rw [Finset.sum_range_succ]; ring
  rw [hG, hP]; unfold poisCdf; ring

lemma dVV_succ (η : ℝ) (i : ℕ) (τ : ℝ) : dVV η (i + 1) τ = η * poisMass τ i - poisCdf τ i := by
  unfold dVV cdfPrev pPrev poisCdf; rfl

lemma rankBound_bdd (μ η : ℝ) (hμ : 0 ≤ μ) (hη : 0 ≤ η) :
    BddBelow (Set.range fun l : ℕ => expectedShortfall μ l + η * poisTail μ l) := by
  refine ⟨0, ?_⟩
  rintro _ ⟨l, rfl⟩
  have h1 : 0 ≤ expectedShortfall μ l := Finset.sum_nonneg (fun n hn => mul_nonneg (by
    have := Finset.mem_range.mp hn; rw [sub_nonneg]; exact_mod_cast Nat.lt_succ_iff.mp this)
    (d2_pm_nonneg μ hμ n))
  have h2 : 0 ≤ poisTail μ l := by
    unfold poisTail
    have := sum_le_hasSum (Finset.range l) (fun n _ => d2_pm_nonneg μ hμ n) (pm_hasSum μ hμ)
    linarith
  positivity

lemma rankBound_le_VV (μ η g : ℝ) (hμ : 0 ≤ μ) (hη : 0 ≤ η) (i : ℕ) :
    rankBound μ η - g ≤ VV η g i μ := by
  unfold rankBound VV
  have := ciInf_le (rankBound_bdd μ η hμ hη) i
  linarith

lemma VV_lower (η g : ℝ) (hη : 0 ≤ η) (i : ℕ) {τ : ℝ} (hτ : 0 ≤ τ) :
    (i : ℝ) - τ - g ≤ VV η g i τ := by
  unfold VV
  have hsum : HasSum (fun n : ℕ => (n : ℝ) * poisMass τ n - (i : ℝ) * poisMass τ n) (τ - i) := by
    have := (pm_mean_hasSum τ hτ).sub ((pm_hasSum τ hτ).mul_left (i : ℝ))
    simpa using this
  have h1 := sum_le_hasSum (Finset.range (i + 1)) (fun n hn => by
    simp only [Finset.mem_range, not_lt] at hn
    have : (i : ℝ) + 1 ≤ n := by exact_mod_cast hn
    nlinarith [d2_pm_nonneg τ hτ n]) hsum
  have h2 : expectedShortfall τ i = -∑ n ∈ Finset.range (i + 1),
      ((n : ℝ) * poisMass τ n - (i : ℝ) * poisMass τ n) := by
    unfold expectedShortfall
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl; intro n _; ring
  have h3 : 0 ≤ poisTail τ i := by
    unfold poisTail
    have := sum_le_hasSum (Finset.range i) (fun n _ => d2_pm_nonneg τ hτ n) (pm_hasSum τ hτ)
    linarith
  nlinarith

lemma VV_upper (η g : ℝ) (hη : 0 ≤ η) (i : ℕ) {τ : ℝ} (hτ : 0 ≤ τ) :
    VV η g i τ ≤ i + η - g := by
  unfold VV
  have hs1 : ∑ n ∈ Finset.range (i + 1), poisMass τ n ≤ 1 :=
    sum_le_hasSum _ (fun n _ => d2_pm_nonneg τ hτ n) (pm_hasSum τ hτ)
  have h1 : expectedShortfall τ i ≤ i := by
    unfold expectedShortfall
    calc ∑ n ∈ Finset.range (i + 1), ((i : ℝ) - n) * poisMass τ n
        ≤ ∑ n ∈ Finset.range (i + 1), (i : ℝ) * poisMass τ n :=
          Finset.sum_le_sum (fun n _ => mul_le_mul_of_nonneg_right (by
            have := Nat.cast_nonneg (α := ℝ) n; linarith) (d2_pm_nonneg τ hτ n))
      _ = (i : ℝ) * ∑ n ∈ Finset.range (i + 1), poisMass τ n := by rw [Finset.mul_sum]
      _ ≤ i := by nlinarith [Nat.cast_nonneg (α := ℝ) i]
  have h2 : poisTail τ i ≤ 1 := by
    unfold poisTail
    have := Finset.sum_nonneg (fun n (_ : n ∈ Finset.range i) => d2_pm_nonneg τ hτ n)
    linarith
  nlinarith

lemma abs_dVV_le (η : ℝ) (hη : 0 ≤ η) (i : ℕ) {τ : ℝ} (hτ : 0 ≤ τ) : |dVV η i τ| ≤ η + 1 := by
  unfold dVV
  have hp0 := pPrev_nonneg τ hτ i
  have hp1 : pPrev i τ ≤ 1 := by
    cases i with
    | zero => simp [pPrev]
    | succ i => exact d2_pm_le_one τ hτ i
  have hc0 : 0 ≤ cdfPrev i τ := Finset.sum_nonneg (fun n _ => d2_pm_nonneg τ hτ n)
  have hc1 : cdfPrev i τ ≤ 1 := sum_le_hasSum _ (fun n _ => d2_pm_nonneg τ hτ n) (pm_hasSum τ hτ)
  rw [abs_le]; constructor <;> nlinarith

end LostSalesRQ

namespace LostSalesRQ

open MeasureTheory ProbabilityTheory Filter Set Topology

lemma integral_congr_Ioo {f g : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (h : ∀ t, a < t → t < b → f t = g t) : ∫ t in a..b, f t = ∫ t in a..b, g t := by
  apply intervalIntegral.integral_congr_ae
  have hne : ∀ᵐ t ∂(volume : Measure ℝ), t ≠ b := by
    rw [ae_iff]; simp
  filter_upwards [hne] with t hne ht
  rw [uIoc_of_le hab] at ht
  exact h t ht.1 (lt_of_le_of_ne ht.2 hne)

lemma ii_congr_Ioo {f g : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b) (hf : IntervalIntegrable f volume a b)
    (h : ∀ t, a < t → t < b → f t = g t) : IntervalIntegrable g volume a b := by
  apply hf.congr_uIoo
  intro t ht
  rw [uIoo_of_le hab] at ht
  exact h t ht.1 ht.2

/-- Piecewise fundamental theorem of calculus for a state that changes only at finitely many
event times. -/
theorem piecewise_ftc {X : Type*} (F : X → ℝ → ℝ) (f : X → ℝ → ℝ)
    (hF : ∀ ξ a b, a ≤ b → F ξ b - F ξ a = ∫ t in a..b, f ξ t)
    (hfi : ∀ ξ a b, IntervalIntegrable (f ξ) volume a b)
    (x xl : ℝ → X) (E : Finset ℝ) :
    ∀ T, 0 ≤ T → (∀ e ∈ E, 0 < e ∧ e ≤ T) →
    (∀ s t, 0 ≤ s → s ≤ t → t ≤ T → (∀ e ∈ E, ¬ (s < e ∧ e ≤ t)) → x t = x s) →
    (∀ e ∈ E, ∃ ε > 0, ∀ s, e - ε < s → s < e → x s = xl e) →
    IntervalIntegrable (fun t => f (x t) t) volume 0 T ∧
    F (x T) T - F (x 0) 0 = (∫ t in (0:ℝ)..T, f (x t) t) + ∑ e ∈ E, (F (x e) e - F (xl e) e) := by
  classical
  induction E using Finset.induction_on_max with
  | empty =>
    intro T hT _ hconst _
    have hx : ∀ t, 0 ≤ t → t ≤ T → x t = x 0 := fun t h1 h2 =>
      hconst 0 t le_rfl h1 h2 (by simp)
    constructor
    · exact ii_congr_Ioo hT (hfi (x 0) 0 T) (fun t h1 h2 => by rw [hx t h1.le h2.le])
    · rw [Finset.sum_empty, add_zero, hx T hT le_rfl, hF (x 0) 0 T hT]
      exact integral_congr_Ioo hT (fun t h1 h2 => by rw [hx t h1.le h2.le])
  | insert a E hlt ih =>
    intro T hT hE hconst hleft
    have haE : a ∉ E := fun h => lt_irrefl a (hlt a h)
    have ha := hE a (Finset.mem_insert_self a E)
    set T' : ℝ := if h : E.Nonempty then E.max' h else 0 with hT'
    have hT'0 : 0 ≤ T' := by
      rw [hT']; split_ifs with h
      · exact (hE _ (Finset.mem_insert_of_mem (E.max'_mem h))).1.le
      · exact le_rfl
    have hT'a : T' < a := by
      rw [hT']; split_ifs with h
      · exact hlt _ (E.max'_mem h)
      · exact ha.1
    have hET' : ∀ e ∈ E, e ≤ T' := fun e he => by
      rw [hT', dif_pos ⟨e, he⟩]; exact E.le_max' e he
    have ih' := ih T' hT'0 (fun e he => ⟨(hE e (Finset.mem_insert_of_mem he)).1, hET' e he⟩)
      (fun s t h1 h2 h3 h4 => hconst s t h1 h2 (le_trans h3 (le_trans hT'a.le ha.2)) (by
        intro e he
        rcases Finset.mem_insert.mp he with rfl | he'
        · rintro ⟨-, h5⟩; linarith
        · exact h4 e he'))
      (fun e he => hleft e (Finset.mem_insert_of_mem he))
    have hc1 : ∀ t, T' ≤ t → t < a → x t = x T' := fun t h1 h2 =>
      hconst T' t hT'0 h1 (le_trans h2.le ha.2) (by
        intro e he
        rcases Finset.mem_insert.mp he with rfl | he'
        · rintro ⟨-, h5⟩; linarith
        · rintro ⟨h5, -⟩; linarith [hET' e he'])
    have hc2 : ∀ t, a ≤ t → t ≤ T → x t = x a := fun t h1 h2 =>
      hconst a t ha.1.le h1 h2 (by
        intro e he
        rcases Finset.mem_insert.mp he with rfl | he'
        · rintro ⟨h5, -⟩; linarith
        · rintro ⟨h5, -⟩; linarith [hlt e he'])
    have hxl : xl a = x T' := by
      obtain ⟨ε, hε, hs⟩ := hleft a (Finset.mem_insert_self a E)
      have h1 : a - ε < max T' (a - ε / 2) := lt_max_of_lt_right (by linarith)
      have h2 : max T' (a - ε / 2) < a := max_lt hT'a (by linarith)
      rw [← hs _ h1 h2, hc1 _ (le_max_left _ _) h2]
    have hi1 : IntervalIntegrable (fun t => f (x t) t) volume T' a :=
      ii_congr_Ioo hT'a.le (hfi (x T') T' a) (fun t h1 h2 => by rw [hc1 t h1.le h2])
    have hi2 : IntervalIntegrable (fun t => f (x t) t) volume a T :=
      ii_congr_Ioo ha.2 (hfi (x a) a T) (fun t h1 h2 => by rw [hc2 t h1.le h2.le])
    have hJ1 : ∫ t in T'..a, f (x t) t = F (x T') a - F (x T') T' := by
      rw [hF (x T') T' a hT'a.le]
      exact integral_congr_Ioo hT'a.le (fun t h1 h2 => by rw [hc1 t h1.le h2])
    have hJ2 : ∫ t in a..T, f (x t) t = F (x a) T - F (x a) a := by
      rw [hF (x a) a T ha.2]
      exact integral_congr_Ioo ha.2 (fun t h1 h2 => by rw [hc2 t h1.le h2.le])
    refine ⟨(ih'.1.trans hi1).trans hi2, ?_⟩
    rw [← intervalIntegral.integral_add_adjacent_intervals (ih'.1.trans hi1) hi2,
      ← intervalIntegral.integral_add_adjacent_intervals ih'.1 hi1, hJ1, hJ2,
      Finset.sum_insert haE, hc2 T ha.2 le_rfl, hxl]
    linarith [ih'.2]

/-- Value of a unit along time, with delivery epoch c. -/
noncomputable def Wt (η g : ℝ) (i : ℕ) (c t : ℝ) : ℝ := VV η g i (max 0 (c - t))

/-- Its time derivative. -/
noncomputable def wt (η : ℝ) (i : ℕ) (c t : ℝ) : ℝ := if t < c then -dVV η i (c - t) else 0

lemma measurable_wt (η : ℝ) (i : ℕ) (c : ℝ) : Measurable (wt η i c) :=
  Measurable.ite measurableSet_Iio
    ((continuous_dVV η i).measurable.comp (measurable_const.sub measurable_id)).neg measurable_const

lemma abs_wt_le (η : ℝ) (hη : 0 ≤ η) (i : ℕ) (c t : ℝ) : |wt η i c t| ≤ η + 1 := by
  unfold wt; split_ifs with h
  · rw [abs_neg]; exact abs_dVV_le η hη i (by linarith)
  · simp; linarith

lemma Wt_ftc (η g : ℝ) (hη : 0 ≤ η) (i : ℕ) (c a b : ℝ) (hab : a ≤ b) :
    Wt η g i c b - Wt η g i c a = ∫ t in a..b, wt η i c t := by
  symm
  apply intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le hab
  · exact ((continuous_VV η g i).comp (continuous_const.max
      (continuous_const.sub continuous_id))).continuousOn
  · intro x _
    by_cases hx : x < c
    · have h1 : HasDerivAt (fun t => VV η g i (c - t)) (dVV η i (c - x) * (-1)) x :=
        (hasDerivAt_VV η g i (c - x)).comp x ((hasDerivAt_id x).const_sub c)
      have h2 : (fun t => Wt η g i c t) =ᶠ[𝓝 x] (fun t => VV η g i (c - t)) := by
        filter_upwards [Iio_mem_nhds hx] with t ht
        unfold Wt; rw [max_eq_right (by linarith [show t < c from ht])]
      have h3 := (h1.congr_of_eventuallyEq h2).hasDerivWithinAt (s := Ioi x)
      unfold wt; rw [if_pos hx]
      convert h3 using 1; ring
    · push Not at hx
      unfold wt; rw [if_neg (not_lt.mpr hx)]
      apply (hasDerivWithinAt_const x (Ioi x) (VV η g i 0)).congr
      · intro y hy
        unfold Wt; rw [max_eq_left (by linarith [show x < y from hy])]
      · unfold Wt; rw [max_eq_left (by linarith)]
  · exact intervalIntegrable_of_bdd (measurable_wt η i c) (abs_wt_le η hη i c) a b

/-- The truncated potential: values of the committed units of ranks 1..M. -/
noncomputable def Fpot (η g μ : ℝ) (M : ℕ) (ς : ℕ → ℝ) (a u : ℕ) (t : ℝ) : ℝ :=
  ∑ i ∈ Finset.range (min (u - a) M), Wt η g (i + 1) (ς (a + 1 + i) + μ) t

noncomputable def fpot (η μ : ℝ) (M : ℕ) (ς : ℕ → ℝ) (a u : ℕ) (t : ℝ) : ℝ :=
  ∑ i ∈ Finset.range (min (u - a) M), wt η (i + 1) (ς (a + 1 + i) + μ) t

lemma fpot_ii (η μ : ℝ) (hη : 0 ≤ η) (M : ℕ) (ς : ℕ → ℝ) (a u : ℕ) (x y : ℝ) :
    IntervalIntegrable (fpot η μ M ς a u) volume x y := by
  unfold fpot
  have : (fun t => ∑ i ∈ Finset.range (min (u - a) M), wt η (i + 1) (ς (a + 1 + i) + μ) t) =
      ∑ i ∈ Finset.range (min (u - a) M), (fun t => wt η (i + 1) (ς (a + 1 + i) + μ) t) := by
    funext t; simp
  rw [this]
  exact IntervalIntegrable.sum _ (fun j _ => intervalIntegrable_of_bdd (measurable_wt _ _ _)
    (abs_wt_le η hη _ _) x y)

lemma Fpot_ftc (η g μ : ℝ) (hη : 0 ≤ η) (M : ℕ) (ς : ℕ → ℝ) (a u : ℕ) (x y : ℝ) (hxy : x ≤ y) :
    Fpot η g μ M ς a u y - Fpot η g μ M ς a u x = ∫ t in x..y, fpot η μ M ς a u t := by
  unfold Fpot fpot
  rw [← Finset.sum_sub_distrib, intervalIntegral.integral_finset_sum (fun j _ =>
    intervalIntegrable_of_bdd (measurable_wt _ _ _) (abs_wt_le η hη _ _) x y)]
  apply Finset.sum_congr rfl
  intro j _
  exact Wt_ftc η g hη _ _ x y hxy

end LostSalesRQ

namespace LostSalesRQ

open MeasureTheory ProbabilityTheory Filter Set Topology

lemma cs_agingSet_bdd (η T : ℝ) (hη : 0 ≤ η) :
    BddAbove {x : ℝ | ∃ (m : ℕ) (τ : Fin m → ℝ), Monotone τ ∧ (∀ i, 0 ≤ τ i ∧ τ i ≤ T) ∧
      x = ∑ i : Fin m, (η * poisMass (τ i) (i : ℕ) - poisCdf (τ i) (i : ℕ))} := by
  refine ⟨η * ((⌊η * T⌋₊ : ℝ) + 1), ?_⟩
  rintro x ⟨m, τ, -, hτ, rfl⟩
  calc ∑ i : Fin m, (η * poisMass (τ i) (i : ℕ) - poisCdf (τ i) (i : ℕ))
      ≤ ∑ i : Fin m, (if (((i : ℕ) : ℝ)) ≤ η * T then η else 0) :=
        Finset.sum_le_sum (fun i _ => aging_term_le η T (τ i) hη (hτ i).1 (hτ i).2 i)
    _ = ∑ i ∈ Finset.range m, (if (i : ℝ) ≤ η * T then η else 0) :=
        Fin.sum_univ_eq_sum_range (fun i => if (i : ℝ) ≤ η * T then η else 0) m
    _ ≤ η * ((⌊η * T⌋₊ : ℝ) + 1) := by
        rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul,
          mul_comm]
        apply mul_le_mul_of_nonneg_left _ hη
        have hsub : ((Finset.range m).filter (fun i : ℕ => (i : ℝ) ≤ η * T)) ⊆
            Finset.range (⌊η * T⌋₊ + 1) := by
          intro i hi
          simp only [Finset.mem_filter, Finset.mem_range] at hi ⊢
          have := Nat.le_floor hi.2
          omega
        have := Finset.card_le_card hsub
        rw [Finset.card_range] at this
        exact_mod_cast this

section rate
variable (η g : ℝ)

lemma Wt_del {i : ℕ} {c t : ℝ} (h : c ≤ t) : Wt η g i c t = VV η g i 0 := by
  unfold Wt; rw [max_eq_left (by linarith)]

lemma Wt_pend {i : ℕ} {c t : ℝ} (h : t < c) : Wt η g i c t = VV η g i (c - t) := by
  unfold Wt; rw [max_eq_right (by linarith)]

lemma step_term {i : ℕ} (hi : 1 ≤ i) (c t : ℝ) :
    (Wt η g i c t - Wt η g (i + 1) c t) + wt η (i + 1) c t = if c ≤ t then -1 else 0 := by
  split_ifs with h
  · rw [Wt_del η g h, Wt_del η g h, VV_zero η g hi, VV_zero η g (by omega)]
    unfold wt; rw [if_neg (not_lt.mpr h)]; push_cast; ring
  · push Not at h
    rw [Wt_pend η g h, Wt_pend η g h, VV_sub_succ]
    unfold wt; rw [if_pos h]; ring

end rate

/-- The pointwise rate inequality behind the committed-supply bound. -/
theorem rate_ineq (η g μ ap : ℝ) (M : ℕ) (hη : 1 ≤ η) (hμ : 0 ≤ μ) (hM1 : 1 ≤ M)
    (hMg : μ + g ≤ M) (hg0 : 0 ≤ g) (hgD : g ≤ ap - agingRateSup μ η)
    (ς : ℕ → ℝ) (t : ℝ) (A u v : ℕ) (hAv : A ≤ v) (hvu : v ≤ u)
    (hς : ∀ j, 1 ≤ j → j ≤ u → ς j ≤ t)
    (hdel : ∀ j, 1 ≤ j → j ≤ u → (j ≤ v ↔ ς j + μ ≤ t))
    (hmono : ∀ j j', 1 ≤ j → j ≤ j' → j' ≤ u → ς j ≤ ς j') :
    g ≤ ((v - A : ℕ) : ℝ) + (ap * (if v ≤ A then 1 else 0) +
      (if A < v then Fpot η g μ M ς (A + 1) u t - Fpot η g μ M ς A u t else 0)) +
      fpot η μ M ς A u t := by
  have hη0 : 0 ≤ η := by linarith
  set n := min (u - A) M with hn
  set c : ℕ → ℝ := fun i => ς (A + 1 + i) + μ with hc
  have hres : ∀ i, i < n → c i - t ≤ μ := fun i hi => by
    have := hς (A + 1 + i) (by omega) (by omega); simp only [hc]; linarith
  by_cases hAv' : A < v
  · rw [if_neg (by omega), if_pos hAv', mul_zero, zero_add]
    have hn1 : 1 ≤ n := by omega
    have hF0 : Fpot η g μ M ς A u t = Wt η g 1 (c 0) t +
        ∑ i ∈ Finset.range (n - 1), Wt η g (i + 2) (c (i + 1)) t := by
      simp only [hc]; unfold Fpot
      rw [← hn, show n = (n - 1) + 1 by omega, Finset.sum_range_succ', add_comm, Nat.add_sub_cancel]
    have hf0 : fpot η μ M ς A u t = wt η 1 (c 0) t +
        ∑ i ∈ Finset.range (n - 1), wt η (i + 2) (c (i + 1)) t := by
      simp only [hc]; unfold fpot
      rw [← hn, show n = (n - 1) + 1 by omega, Finset.sum_range_succ', add_comm, Nat.add_sub_cancel]
    set n' := min (u - (A + 1)) M with hn'
    have hF1 : Fpot η g μ M ς (A + 1) u t =
        ∑ i ∈ Finset.range n', Wt η g (i + 1) (c (i + 1)) t := by
      simp only [hc]; unfold Fpot; rw [← hn']
      apply Finset.sum_congr rfl; intro i _
      rw [show A + 1 + 1 + i = A + 1 + (i + 1) by ring]
    have hnn' : n - 1 ≤ n' := by omega
    have hsplit := Finset.sum_range_add_sum_Ico (fun i => Wt η g (i + 1) (c (i + 1)) t) hnn'
    have hdel0 : c 0 ≤ t := by
      have := (hdel (A + 1) (by omega) (by omega)).mp (by omega)
      simp only [hc]; simpa using this
    have hW1 : Wt η g 1 (c 0) t = 1 - g := by rw [Wt_del η g hdel0, VV_zero η g le_rfl]; simp
    have hw1 : wt η 1 (c 0) t = 0 := by unfold wt; rw [if_neg (not_lt.mpr hdel0)]
    have hmid : ∑ i ∈ Finset.range (n - 1), ((Wt η g (i + 1) (c (i + 1)) t -
        Wt η g (i + 2) (c (i + 1)) t) + wt η (i + 2) (c (i + 1)) t) =
        -(min (n - 1) (v - A - 1) : ℕ) := by
      have : ∀ i ∈ Finset.range (n - 1), ((Wt η g (i + 1) (c (i + 1)) t -
          Wt η g (i + 2) (c (i + 1)) t) + wt η (i + 2) (c (i + 1)) t) =
          if A + 1 + (i + 1) ≤ v then -1 else 0 := by
        intro i hi
        rw [step_term η g (by omega)]
        have hi' := Finset.mem_range.mp hi
        have := hdel (A + 1 + (i + 1)) (by omega) (by omega)
        simp only [hc]
        by_cases h : A + 1 + (i + 1) ≤ v
        · rw [if_pos (this.mp h), if_pos h]
        · rw [if_neg (fun h' => h (this.mpr h')), if_neg h]
      rw [Finset.sum_congr rfl this, Finset.sum_ite, Finset.sum_const_zero, add_zero,
        Finset.sum_const, nsmul_eq_mul, mul_neg, mul_one]
      congr 2
      have : (Finset.range (n - 1)).filter (fun i => A + 1 + (i + 1) ≤ v) =
          Finset.range (min (n - 1) (v - A - 1)) := by
        ext i; simp only [Finset.mem_filter, Finset.mem_range]; omega
      rw [this, Finset.card_range]
    have hextra : 0 ≤ ∑ i ∈ Finset.Ico (n - 1) n', Wt η g (i + 1) (c (i + 1)) t := by
      apply Finset.sum_nonneg; intro i hi
      have hi' := Finset.mem_Ico.mp hi
      have hiM : i + 1 = M := by omega
      have hr : c (i + 1) - t ≤ μ := by
        have := hς (A + 1 + (i + 1)) (by omega) (by omega); simp only [hc]; linarith
      have hmax : max 0 (c (i + 1) - t) ≤ μ := max_le hμ hr
      unfold Wt
      have := VV_lower η g hη0 (i + 1) (le_max_left 0 (c (i + 1) - t))
      have hcast : ((i + 1 : ℕ) : ℝ) = M := by exact_mod_cast hiM
      linarith
    rw [hF0, hf0, hF1, ← hsplit, hW1, hw1]
    have hrew : ∑ i ∈ Finset.range (n - 1), Wt η g (i + 1) (c (i + 1)) t +
        ∑ i ∈ Finset.Ico (n - 1) n', Wt η g (i + 1) (c (i + 1)) t -
        (1 - g + ∑ i ∈ Finset.range (n - 1), Wt η g (i + 2) (c (i + 1)) t) +
        (0 + ∑ i ∈ Finset.range (n - 1), wt η (i + 2) (c (i + 1)) t) =
        g - 1 + ∑ i ∈ Finset.range (n - 1), ((Wt η g (i + 1) (c (i + 1)) t -
          Wt η g (i + 2) (c (i + 1)) t) + wt η (i + 2) (c (i + 1)) t) +
        ∑ i ∈ Finset.Ico (n - 1) n', Wt η g (i + 1) (c (i + 1)) t := by
      rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]; ring
    rw [hmid] at hrew
    by_cases hIn : v - A ≤ n
    · have h1 : min (n - 1) (v - A - 1) = v - A - 1 := by omega
      rw [h1] at hrew
      have h2 : (((v - A - 1 : ℕ)) : ℝ) = ((v - A : ℕ) : ℝ) - 1 := by
        rw [Nat.cast_sub (show 1 ≤ v - A by omega)]; simp
      rw [h2] at hrew
      linarith
    · push Not at hIn
      have hnM : n = M := by omega
      have hn'M : n' = M := by omega
      have h1 : min (n - 1) (v - A - 1) = M - 1 := by omega
      rw [h1] at hrew
      have hex : ∑ i ∈ Finset.Ico (n - 1) n', Wt η g (i + 1) (c (i + 1)) t = M - g := by
        rw [hnM, hn'M]
        rw [show Finset.Ico (M - 1) M = {M - 1} by
          ext i; simp only [Finset.mem_Ico, Finset.mem_singleton]; omega, Finset.sum_singleton]
        have hd : c (M - 1 + 1) ≤ t := by
          have := (hdel (A + 1 + (M - 1 + 1)) (by omega) (by omega)).mp (by omega)
          simp only [hc]; exact this
        rw [Wt_del η g hd, VV_zero η g (by omega), show M - 1 + 1 = M by omega]
      rw [hex] at hrew
      have hvA : ((v - A : ℕ) : ℝ) ≥ M + 1 := by
        have : M + 1 ≤ v - A := by omega
        exact_mod_cast this
      have h3 : (((M - 1 : ℕ)) : ℝ) = (M : ℝ) - 1 := by rw [Nat.cast_sub hM1]; simp
      rw [h3] at hrew
      linarith
  · -- stockout
    push Not at hAv'
    have hvA : v = A := le_antisymm hAv' hAv
    rw [if_pos hAv', if_neg (by omega), add_zero, mul_one, show v - A = 0 by omega,
      Nat.cast_zero, zero_add]
    have hpend : ∀ i, i < n → t < c i := by
      intro i hi
      by_contra h; push Not at h
      have := (hdel (A + 1 + i) (by omega) (by omega)).mpr (by simp only [hc] at h; exact h)
      omega
    set τ : Fin n → ℝ := fun i => c i - t with hτ
    have hτm : Monotone τ := by
      intro i i' hii'
      simp only [hτ, hc]
      have := hmono (A + 1 + i) (A + 1 + i') (by omega) (by
        have : (i : ℕ) ≤ i' := hii'; omega) (by have := i'.2; omega)
      linarith
    have hτb : ∀ i, 0 ≤ τ i ∧ τ i ≤ μ := fun i =>
      ⟨by simp only [hτ]; linarith [hpend i i.2], hres i i.2⟩
    have hD := le_csSup (cs_agingSet_bdd η μ hη0) ⟨n, τ, hτm, hτb, rfl⟩
    have hf : fpot η μ M ς A u t = -∑ i : Fin n,
        (η * poisMass (τ i) (i : ℕ) - poisCdf (τ i) (i : ℕ)) := by
      unfold fpot
      rw [← hn, ← Finset.sum_neg_distrib, ← Fin.sum_univ_eq_sum_range
        (fun i => wt η (i + 1) (ς (A + 1 + i) + μ) t) n]
      apply Finset.sum_congr rfl; intro i _
      unfold wt; rw [if_pos (hpend i i.2), dVV_succ]
    rw [hf]
    unfold agingRateSup at hgD
    linarith

/-- Orders never lower the potential. -/
lemma Fpot_le_orders (η g μ : ℝ) (M : ℕ) (ς : ℕ → ℝ) (t : ℝ) (A u' u : ℕ) (hu : u' ≤ u)
    (hnew : ∀ j, u' < j → j ≤ u → ς j = t) (hV : ∀ i, 1 ≤ i → 0 ≤ VV η g i μ) (hμ : 0 ≤ μ) :
    Fpot η g μ M ς A u' t ≤ Fpot η g μ M ς A u t := by
  unfold Fpot
  have hle : min (u' - A) M ≤ min (u - A) M := by omega
  rw [← Finset.sum_range_add_sum_Ico _ hle]
  have : 0 ≤ ∑ i ∈ Finset.Ico (min (u' - A) M) (min (u - A) M),
      Wt η g (i + 1) (ς (A + 1 + i) + μ) t := by
    apply Finset.sum_nonneg; intro i hi
    have hi' := Finset.mem_Ico.mp hi
    rw [hnew (A + 1 + i) (by omega) (by omega)]
    unfold Wt; rw [show t + μ - t = μ by ring, max_eq_right hμ]
    exact hV (i + 1) (by omega)
  linarith

/-- Bound on the potential. -/
lemma abs_Fpot_le (η g μ : ℝ) (hη : 0 ≤ η) (hμ : 0 ≤ μ) (M : ℕ) (ς : ℕ → ℝ) (t : ℝ) (A u : ℕ)
    (hς : ∀ i, i < min (u - A) M → ς (A + 1 + i) ≤ t) :
    |Fpot η g μ M ς A u t| ≤ M * (M + μ + η + |g|) := by
  unfold Fpot
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  calc ∑ i ∈ Finset.range (min (u - A) M), |Wt η g (i + 1) (ς (A + 1 + i) + μ) t|
      ≤ ∑ i ∈ Finset.range (min (u - A) M), ((M : ℝ) + μ + η + |g|) := by
        apply Finset.sum_le_sum; intro i hi
        have hi' := Finset.mem_range.mp hi
        have hr0 : 0 ≤ max 0 (ς (A + 1 + i) + μ - t) := le_max_left _ _
        have hr1 : max 0 (ς (A + 1 + i) + μ - t) ≤ μ := by
          have := hς i hi'; exact max_le hμ (by linarith)
        have h1 := VV_lower η g hη (i + 1) hr0
        have h2 := VV_upper η g hη (i + 1) hr0
        have hiM : ((i + 1 : ℕ) : ℝ) ≤ M := by exact_mod_cast (show i + 1 ≤ M by omega)
        have hg := le_abs_self g
        have hg' := neg_abs_le g
        have hi0 : (0 : ℝ) ≤ ((i + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
        unfold Wt; rw [abs_le]
        constructor <;> linarith
    _ ≤ M * (M + μ + η + |g|) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        apply mul_le_mul_of_nonneg_right (by exact_mod_cast min_le_right _ _)
        have := abs_nonneg g; positivity

end LostSalesRQ

namespace LostSalesRQ

open MeasureTheory ProbabilityTheory Filter Set Topology

lemma measurable_sel {α : Type*} {_ : MeasurableSpace α} {β : Type*} [Countable β]
    [MeasurableSpace β] [MeasurableSingletonClass β] {G : β → α → ℝ} (hG : ∀ b, Measurable (G b))
    {K : α → β} (hK : Measurable K) : Measurable (fun x => G (K x) x) :=
  (measurable_from_prod_countable_left (f := fun p : α × β => G p.2 p.1) hG).comp
    (measurable_id.prodMk hK)

section strict
variable {f : ℝ → ℕ}

lemma arrT_spec' (hf : RegPath f) (h0 : ∀ s, s < 0 → f s = 0) {k : ℕ} (hk : 1 ≤ k) {t : ℝ}
    (hkt : k ≤ f t) (s : ℝ) : k ≤ f s ↔ arrT f k ≤ s := by
  have hbdd : BddBelow {s | k ≤ f s} := ⟨0, fun z hz => by
    by_contra h; push Not at h; have := h0 z h; simp only [mem_ofPred_eq] at hz; omega⟩
  have hmem : k ≤ f (arrT f k) := by
    obtain ⟨δ, hδ, hc⟩ := hf.2 (arrT f k)
    obtain ⟨z, hz, hzl⟩ := exists_lt_of_csInf_lt ⟨t, hkt⟩ (show sInf {s | k ≤ f s} < arrT f k + δ by
      unfold arrT; linarith)
    have : arrT f k ≤ z := csInf_le hbdd hz
    rw [← hc z this hzl]; exact hz
  constructor
  · intro h; exact csInf_le hbdd h
  · intro h; exact le_trans hmem (hf.1 h)

lemma arrT_eq_epoch' (hf : RegPath f) (h0 : ∀ s, s < 0 → f s = 0) {τ : ℝ} {k : ℕ}
    (hk1 : leftLim f τ < k) (hk2 : k ≤ f τ) : arrT f k = τ := by
  have hk : 1 ≤ k := by omega
  apply le_antisymm ((arrT_spec' hf h0 hk hk2 τ).mp hk2)
  by_contra h; push Not at h
  have := le_leftLim hf.1 h
  have := (arrT_spec' hf h0 hk hk2 (arrT f k)).mpr le_rfl
  omega

lemma arrT_mono' (hf : RegPath f) (h0 : ∀ s, s < 0 → f s = 0) {k k' : ℕ} (hk : 1 ≤ k)
    (hkk : k ≤ k') {t : ℝ} (hkt : k' ≤ f t) : arrT f k ≤ arrT f k' := by
  have h1 := (arrT_spec' hf h0 (le_trans hk hkk) hkt (arrT f k')).mpr le_rfl
  exact (arrT_spec' hf h0 hk (le_trans hkk hkt) _).mp (le_trans hkk h1)

end strict

lemma leftLim_nonpos {f : ℝ → ℕ} (hf : Monotone f) (h0 : ∀ s, s < 0 → f s = 0) {t : ℝ}
    (ht : t ≤ 0) : leftLim f t = 0 := by
  obtain ⟨s0, hs0, he⟩ := leftLim_attained hf t
  rw [← he s0 le_rfl hs0, h0 s0 (by linarith)]

/-! ### The virtual empty system on a path -/

section pathsys
variable (μ : ℝ) (N U : ℝ → ℕ)

/-- Units available (delivered) just before the k-th demand in the empty system. -/
noncomputable def vAv (k : ℕ) : ℕ := leftLim U (arrT N k - μ)

/-- Demands served among the first k in the empty system. -/
noncomputable def vS (k : ℕ) : ℕ := srec (vAv μ N U) k

/-- Served demands by time t in the empty system. -/
noncomputable def vA (t : ℝ) : ℕ := vS μ N U (N t)

/-- Standing assumptions on the two paths. -/
structure PathOK : Prop where
  hN : RegPath N
  hN0 : ∀ s, s ≤ 0 → N s = 0
  hU : RegPath U
  hU0 : ∀ s, s < 0 → U s = 0
  hμ : 0 ≤ μ

variable {μ N U}

lemma srec_le_av (av : ℕ → ℕ) (n : ℕ) (hmono : ∀ k k', 1 ≤ k → k ≤ k' → k' ≤ n → av k ≤ av k') :
    ∀ k, 1 ≤ k → k ≤ n → srec av k ≤ av k := by
  intro k
  induction k with
  | zero => intro h; omega
  | succ k ih =>
    intro _ hkn
    simp only [srec]
    split_ifs with h
    · omega
    · rcases Nat.eq_zero_or_pos k with hk | hk
      · subst hk; simp [srec]
      · have := ih hk (by omega)
        have := hmono k (k + 1) hk (by omega) hkn
        omega

lemma vAv_mono (h : PathOK μ N U) {T : ℝ} {k k' : ℕ} (hk : 1 ≤ k) (hkk : k ≤ k')
    (hk'T : k' ≤ N T) : vAv μ N U k ≤ vAv μ N U k' := by
  unfold vAv
  apply leftLim_mono h.hU.1
  have := arrT_mono' h.hN (fun s hs => h.hN0 s hs.le) hk hkk hk'T
  linarith

lemma vS_le_vAv (h : PathOK μ N U) {T : ℝ} {k : ℕ} (hk : 1 ≤ k) (hkT : k ≤ N T) :
    vS μ N U k ≤ vAv μ N U k :=
  srec_le_av _ (N T) (fun k k' h1 h2 h3 => vAv_mono h h1 h2 h3) k hk hkT

/-- In the empty system, served demand never exceeds deliveries. -/
lemma vA_le (h : PathOK μ N U) (t : ℝ) : vA μ N U t ≤ U (t - μ) := by
  unfold vA
  rcases Nat.eq_zero_or_pos (N t) with h0 | hpos
  · rw [h0]; simp [vS, srec]
  · refine le_trans (vS_le_vAv h hpos le_rfl) ?_
    unfold vAv
    have hσ := arrT_le h.hN h.hN0 hpos (le_refl (N t))
    exact le_trans (leftLim_le_self h.hU.1 _) (h.hU.1 (by linarith))

lemma vA_le_left (h : PathOK μ N U) {e : ℝ} : vA μ N U e ≤ leftLim U e := by
  unfold vA
  rcases Nat.eq_zero_or_pos (N e) with h0 | hpos
  · rw [h0]; simp [vS, srec]
  · refine le_trans (vS_le_vAv h hpos le_rfl) ?_
    unfold vAv
    have hσ := arrT_le h.hN h.hN0 hpos (le_refl (N e))
    exact leftLim_mono h.hU.1 (by linarith [h.hμ])

/-- The facts about pending units needed by the rate inequality. -/
lemma unit_facts (h : PathOK μ N U) (t : ℝ) :
    (∀ j, 1 ≤ j → j ≤ U t → arrT U j ≤ t) ∧
    (∀ j, 1 ≤ j → j ≤ U t → (j ≤ U (t - μ) ↔ arrT U j + μ ≤ t)) ∧
    (∀ j j', 1 ≤ j → j ≤ j' → j' ≤ U t → arrT U j ≤ arrT U j') := by
  refine ⟨fun j hj hjt => (arrT_spec' h.hU h.hU0 hj hjt t).mp hjt, fun j hj hjt => ?_,
    fun j j' hj hjj hj't => arrT_mono' h.hU h.hU0 hj hjj hj't⟩
  rw [arrT_spec' h.hU h.hU0 hj hjt]; constructor <;> intro <;> linarith

end pathsys

end LostSalesRQ

namespace LostSalesRQ

open MeasureTheory ProbabilityTheory Filter Set Topology

lemma continuous_Fpot (η g μ : ℝ) (M : ℕ) (ς : ℕ → ℝ) (a u : ℕ) :
    Continuous (Fpot η g μ M ς a u) := by
  unfold Fpot Wt
  exact continuous_finset_sum _ (fun i _ => (continuous_VV η g _).comp
    (continuous_const.max (continuous_const.sub continuous_id)))

/-- Demand-and-loss integrand as a function of the state. -/
noncomputable def Psi (η g μ ap : ℝ) (M : ℕ) (ς : ℕ → ℝ) (a u v : ℕ) (t : ℝ) : ℝ :=
  ap * (if v ≤ a then 1 else 0) +
    (if a < v then Fpot η g μ M ς (a + 1) u t - Fpot η g μ M ς a u t else 0)

lemma continuous_Psi (η g μ ap : ℝ) (M : ℕ) (ς : ℕ → ℝ) (a u v : ℕ) :
    Continuous (Psi η g μ ap M ς a u v) := by
  unfold Psi
  apply continuous_const.add
  split_ifs
  · exact (continuous_Fpot _ _ _ _ _ _ _).sub (continuous_Fpot _ _ _ _ _ _ _)
  · exact continuous_const

lemma abs_Psi_le (η g μ ap : ℝ) (hη : 0 ≤ η) (hμ : 0 ≤ μ) (hap : 0 ≤ ap) (M : ℕ) (ς : ℕ → ℝ)
    (a u v : ℕ) (t : ℝ) (hς : ∀ j, 1 ≤ j → j ≤ u → ς j ≤ t) :
    |Psi η g μ ap M ς a u v t| ≤ ap + 2 * (M * (M + μ + η + |g|)) := by
  have h1 := abs_Fpot_le η g μ hη hμ M ς t (a + 1) u (fun i hi => hς _ (by omega) (by omega))
  have h2 := abs_Fpot_le η g μ hη hμ M ς t a u (fun i hi => hς _ (by omega) (by omega))
  unfold Psi
  have hc : |ap * (if v ≤ a then (1 : ℝ) else 0)| ≤ ap := by
    split_ifs <;> simp [abs_of_nonneg hap, hap]
  have hd : |(if a < v then Fpot η g μ M ς (a + 1) u t - Fpot η g μ M ς a u t else 0)| ≤
      2 * (M * (M + μ + η + |g|)) := by
    split_ifs
    · calc _ ≤ |Fpot η g μ M ς (a + 1) u t| + |Fpot η g μ M ς a u t| := abs_sub _ _
        _ ≤ _ := by linarith
    · simp only [abs_zero]
      have := abs_nonneg g
      positivity
  exact le_trans (abs_add_le _ _) (by linarith)

section pw
variable {μ : ℝ} {N U : ℝ → ℕ}

/-- The integrand evaluated along the path. -/
noncomputable def Hpath (η g μ ap : ℝ) (M : ℕ) (N U : ℝ → ℕ) (t : ℝ) : ℝ :=
  Psi η g μ ap M (arrT U) (vA μ N U t) (U t) (U (t - μ)) t

/-- Its left limit at the k-th demand. -/
noncomputable def Hlpath (η g μ ap : ℝ) (M : ℕ) (N U : ℝ → ℕ) (k : ℕ) : ℝ :=
  Psi η g μ ap M (arrT U) (vS μ N U (leftLim N (arrT N k))) (leftLim U (arrT N k))
    (vAv μ N U k) (arrT N k)

lemma lost_sum (μ : ℝ) (N U : ℝ → ℕ) (n : ℕ) :
    (n : ℝ) - vS μ N U n = ∑ k ∈ Finset.Icc 1 n,
      (if vAv μ N U k ≤ vS μ N U (k - 1) then (1 : ℝ) else 0) := by
  induction n with
  | zero => simp [vS, srec]
  | succ n ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ← ih, Nat.add_sub_cancel]
    unfold vS; simp only [srec]
    split_ifs with h1 h2 h2 <;> push_cast <;> first | omega | ring | (exfalso; omega)

theorem pathwise_bound (η g μ ap : ℝ) (M : ℕ) (h : PathOK μ N U) {T : ℝ} (hT : 0 < T)
    (hgood : ∀ τ, 0 < τ → τ ≤ T → N τ ≤ leftLim N τ + 1)
    (hη : 1 ≤ η) (hg0 : 0 ≤ g) (hgB : g ≤ rankBound μ η) (hgD : g ≤ ap - agingRateSup μ η)
    (hM1 : 1 ≤ M) (hMg : μ + g ≤ M) (hap : 0 ≤ ap) :
    IntervalIntegrable (fun t => ((U (t - μ) - vA μ N U t : ℕ) : ℝ)) volume 0 T ∧
    IntervalIntegrable (Hpath η g μ ap M N U) volume 0 T ∧
    g * T - 2 * (M * (M + μ + η + |g|)) +
        (∑ k ∈ Finset.Icc 1 (N T), Hlpath η g μ ap M N U k - ∫ t in (0:ℝ)..T, Hpath η g μ ap M N U t)
      ≤ (∫ t in (0:ℝ)..T, ((U (t - μ) - vA μ N U t : ℕ) : ℝ)) + ap * ((N T : ℝ) - vS μ N U (N T)) := by
  have hη0 : 0 ≤ η := by linarith
  have hμ := h.hμ
  set ς := arrT U with hς
  set Cp := (M : ℝ) * (M + μ + η + |g|) with hCp
  -- measurability in time
  have hNm : Measurable N := h.hN.1.measurable
  have hUm : Measurable U := h.hU.1.measurable
  have hvAm : Measurable (vA μ N U) := (measurable_from_nat (f := vS μ N U)).comp hNm
  have hUmu : Measurable (fun t => U (t - μ)) := hUm.comp (measurable_id.sub_const μ)
  have hIm : Measurable (fun t => ((U (t - μ) - vA μ N U t : ℕ) : ℝ)) :=
    (measurable_from_nat (f := fun n : ℕ => (n : ℝ))).comp (hUmu.sub hvAm)
  have hHm : Measurable (Hpath η g μ ap M N U) := by
    have := measurable_sel (β := ℕ × ℕ × ℕ)
      (G := fun b t => Psi η g μ ap M ς b.1 b.2.1 b.2.2 t)
      (fun b => (continuous_Psi η g μ ap M ς _ _ _).measurable)
      (K := fun t => (vA μ N U t, U t, U (t - μ))) (hvAm.prodMk (hUm.prodMk hUmu))
    exact this
  have hUfacts := unit_facts h
  have hHb : ∀ t, |Hpath η g μ ap M N U t| ≤ ap + 2 * Cp := fun t =>
    abs_Psi_le η g μ ap hη0 hμ hap M ς _ _ _ t (fun j hj hju => (hUfacts t).1 j hj hju)
  have hHi : IntervalIntegrable (Hpath η g μ ap M N U) volume 0 T :=
    intervalIntegrable_of_bdd hHm hHb 0 T
  have hIi : IntervalIntegrable (fun t => ((U (t - μ) - vA μ N U t : ℕ) : ℝ)) volume 0 T := by
    rw [intervalIntegrable_iff]
    refine Measure.integrableOn_of_bounded (M := (U T : ℝ)) (by simp) hIm.aestronglyMeasurable ?_
    rw [uIoc_of_le hT.le]
    refine ae_restrict_of_forall_mem measurableSet_Ioc (fun t ht => ?_)
    rw [Real.norm_eq_abs, Nat.abs_cast]
    have : U (t - μ) - vA μ N U t ≤ U T := le_trans (Nat.sub_le _ _) (h.hU.1 (by linarith [ht.2]))
    exact_mod_cast this
  refine ⟨hIi, hHi, ?_⟩
  -- the potential identity
  set EN := (epochSet_finite h.hN.1 T).toFinset with hEN
  set EU := (epochSet_finite h.hU.1 T).toFinset with hEU
  set E := EN ∪ EU with hE
  have hEmem : ∀ e ∈ E, (0 < e ∧ e ≤ T) := by
    intro e he
    rcases Finset.mem_union.mp he with h1 | h1
    · exact (Set.Finite.mem_toFinset _).mp h1 |>.1
    · exact (Set.Finite.mem_toFinset _).mp h1 |>.1
  have hpw := piecewise_ftc (X := ℕ × ℕ) (fun ξ t => Fpot η g μ M ς ξ.1 ξ.2 t)
    (fun ξ t => fpot η μ M ς ξ.1 ξ.2 t)
    (fun ξ a b hab => Fpot_ftc η g μ hη0 M ς ξ.1 ξ.2 a b hab)
    (fun ξ a b => fpot_ii η μ hη0 M ς ξ.1 ξ.2 a b)
    (fun t => (vA μ N U t, U t)) (fun e => (vS μ N U (leftLim N e), leftLim U e)) E T hT.le hEmem
    (by
      intro s t hs hst htT hno
      have hN' : N t = N s := const_of_noEpoch h.hN hs hst (fun τ h1 h2 h3 =>
        hno τ (Finset.mem_union_left _ ((Set.Finite.mem_toFinset _).mpr
          ⟨⟨by linarith, le_trans h2 htT⟩, h3⟩)) ⟨h1, h2⟩)
      have hU' : U t = U s := const_of_noEpoch h.hU hs hst (fun τ h1 h2 h3 =>
        hno τ (Finset.mem_union_right _ ((Set.Finite.mem_toFinset _).mpr
          ⟨⟨by linarith, le_trans h2 htT⟩, h3⟩)) ⟨h1, h2⟩)
      simp only [vA, hN', hU'])
    (by
      intro e _
      obtain ⟨s1, hs1, he1⟩ := leftLim_attained h.hN.1 e
      obtain ⟨s2, hs2, he2⟩ := leftLim_attained h.hU.1 e
      refine ⟨e - max s1 s2, by linarith [max_lt hs1 hs2], fun s hs1' hs2' => ?_⟩
      have h1 : s1 ≤ s := by linarith [le_max_left s1 s2]
      have h2 : s2 ≤ s := by linarith [le_max_right s1 s2]
      simp only [vA, he1 s h1 hs2', he2 s h2 hs2'])
  obtain ⟨hfi, hpot⟩ := hpw
  -- rate inequality integrated
  have hrate : ∀ t, 0 ≤ t → g ≤ ((U (t - μ) - vA μ N U t : ℕ) : ℝ) + Hpath η g μ ap M N U t +
      fpot η μ M ς (vA μ N U t) (U t) t := by
    intro t _
    exact rate_ineq η g μ ap M hη hμ hM1 hMg hg0 hgD ς t (vA μ N U t) (U t) (U (t - μ))
      (vA_le h t) (h.hU.1 (by linarith)) (hUfacts t).1 (hUfacts t).2.1 (hUfacts t).2.2
  have hint : g * T ≤ (∫ t in (0:ℝ)..T, ((U (t - μ) - vA μ N U t : ℕ) : ℝ)) +
      (∫ t in (0:ℝ)..T, Hpath η g μ ap M N U t) +
      ∫ t in (0:ℝ)..T, fpot η μ M ς (vA μ N U t) (U t) t := by
    rw [← intervalIntegral.integral_add hIi hHi, ← intervalIntegral.integral_add (hIi.add hHi) hfi]
    have := intervalIntegral.integral_mono_on hT.le intervalIntegrable_const
      ((hIi.add hHi).add hfi) (fun t ht => hrate t ht.1)
    simpa [mul_comm] using this
  -- jumps
  have hV : ∀ i, 1 ≤ i → 0 ≤ VV η g i μ := fun i _ => by
    have := rankBound_le_VV μ η g hμ hη0 i; linarith
  set D : ℝ → ℝ := fun e => Fpot η g μ M ς (vA μ N U e) (leftLim U e) e -
    Fpot η g μ M ς (vS μ N U (leftLim N e)) (leftLim U e) e with hD
  have hjump : ∀ e ∈ E, D e ≤ Fpot η g μ M ς (vA μ N U e) (U e) e -
      Fpot η g μ M ς (vS μ N U (leftLim N e)) (leftLim U e) e := by
    intro e he
    have := Fpot_le_orders η g μ M ς e (vA μ N U e) (leftLim U e) (U e)
      (leftLim_le_self h.hU.1 e) (fun j h1 h2 => arrT_eq_epoch' h.hU h.hU0 h1 h2) hV hμ
    simp only [hD]; linarith
  -- demand jumps vanish off demand epochs
  have hD0 : ∀ e ∈ E, e ∉ EN → D e = 0 := by
    intro e he heN
    have hmem := hEmem e he
    have : leftLim N e = N e := by
      by_contra hne
      exact heN ((Set.Finite.mem_toFinset _).mpr ⟨⟨hmem.1, hmem.2⟩,
        lt_of_le_of_ne (leftLim_le_self h.hN.1 e) hne⟩)
    simp only [hD, vA, this, sub_self]
  set rr : ℕ → ℝ := fun k => if vS μ N U (k - 1) < vAv μ N U k then
      Fpot η g μ M ς (vS μ N U (k - 1) + 1) (leftLim U (arrT N k)) (arrT N k) -
      Fpot η g μ M ς (vS μ N U (k - 1)) (leftLim U (arrT N k)) (arrT N k) else 0 with hrr
  have hNsum : ∑ e ∈ EN, D e = ∑ k ∈ Finset.Icc 1 (N T), rr k := by
    apply Finset.sum_nbij' (fun e => N e) (fun k => arrT N k)
    · intro e he
      have he' := (Set.Finite.mem_toFinset _).mp he
      rw [Finset.mem_Icc]
      exact ⟨by have := he'.2; omega, h.hN.1 he'.1.2⟩
    · intro k hk
      have hk' := Finset.mem_Icc.mp hk
      apply (Set.Finite.mem_toFinset _).mpr
      have hσ0 := arrT_pos h.hN h.hN0 hk'.1 hk'.2
      have hσT := arrT_le h.hN h.hN0 hk'.1 hk'.2
      refine ⟨⟨hσ0, hσT⟩, ?_⟩
      have h1 := (arrT_spec h.hN h.hN0 hk'.1 hk'.2 (arrT N k)).mpr le_rfl
      have h2 : leftLim N (arrT N k) < k := by
        obtain ⟨s0, hs0, he0⟩ := leftLim_attained h.hN.1 (arrT N k)
        rw [← he0 s0 le_rfl hs0]
        by_contra hc; push Not at hc
        have := (arrT_spec h.hN h.hN0 hk'.1 hk'.2 s0).mp hc
        linarith
      omega
    · intro e he
      have he' := (Set.Finite.mem_toFinset _).mp he
      exact arrT_eq_epoch h.hN h.hN0 he'.2 le_rfl
    · intro k hk
      have hk' := Finset.mem_Icc.mp hk
      have h1 := (arrT_spec h.hN h.hN0 hk'.1 hk'.2 (arrT N k)).mpr le_rfl
      have hσ0 := arrT_pos h.hN h.hN0 hk'.1 hk'.2
      have hσT := arrT_le h.hN h.hN0 hk'.1 hk'.2
      have h2 : leftLim N (arrT N k) < k := by
        obtain ⟨s0, hs0, he0⟩ := leftLim_attained h.hN.1 (arrT N k)
        rw [← he0 s0 le_rfl hs0]
        by_contra hc; push Not at hc
        have := (arrT_spec h.hN h.hN0 hk'.1 hk'.2 s0).mp hc
        linarith
      have := hgood _ hσ0 hσT
      omega
    · intro e he
      have he' := (Set.Finite.mem_toFinset _).mp he
      have hk := he'.2
      have hgd := hgood e he'.1.1 he'.1.2
      have hl : leftLim N e = N e - 1 := by omega
      have hσ : arrT N (N e) = e := arrT_eq_epoch h.hN h.hN0 hk le_rfl
      simp only [hD, hrr, hσ, vA, hl]
      have hsucc : vS μ N U (N e) = vS μ N U (N e - 1) +
          if vS μ N U (N e - 1) < vAv μ N U (N e) then 1 else 0 := by
        unfold vS
        conv_lhs => rw [show N e = (N e - 1) + 1 by omega]
        simp only [srec]
        rw [show N e - 1 + 1 = N e by omega]
      rw [hsucc]
      split_ifs <;> simp
  have hEsum : ∑ e ∈ E, D e = ∑ e ∈ EN, D e := by
    symm
    apply Finset.sum_subset Finset.subset_union_left
    intro e he heN
    exact hD0 e he heN
  have hjsum : ∑ k ∈ Finset.Icc 1 (N T), rr k ≤ ∑ e ∈ E,
      (Fpot η g μ M ς (vA μ N U e) (U e) e -
        Fpot η g μ M ς (vS μ N U (leftLim N e)) (leftLim U e) e) := by
    rw [← hNsum, ← hEsum]
    exact Finset.sum_le_sum hjump
  -- Hl decomposition on good paths
  have hHl : ∀ k ∈ Finset.Icc 1 (N T), Hlpath η g μ ap M N U k =
      ap * (if vAv μ N U k ≤ vS μ N U (k - 1) then 1 else 0) + rr k := by
    intro k hk
    have hk' := Finset.mem_Icc.mp hk
    have hσ0 := arrT_pos h.hN h.hN0 hk'.1 hk'.2
    have hσT := arrT_le h.hN h.hN0 hk'.1 hk'.2
    have h1 := (arrT_spec h.hN h.hN0 hk'.1 hk'.2 (arrT N k)).mpr le_rfl
    have h2 : leftLim N (arrT N k) < k := by
      obtain ⟨s0, hs0, he0⟩ := leftLim_attained h.hN.1 (arrT N k)
      rw [← he0 s0 le_rfl hs0]
      by_contra hc; push Not at hc
      have := (arrT_spec h.hN h.hN0 hk'.1 hk'.2 s0).mp hc
      linarith
    have := hgood _ hσ0 hσT
    have hl : leftLim N (arrT N k) = k - 1 := by omega
    unfold Hlpath Psi
    rw [hl]
  have hlost := lost_sum μ N U (N T)
  have hHlsum : ∑ k ∈ Finset.Icc 1 (N T), Hlpath η g μ ap M N U k =
      ap * ((N T : ℝ) - vS μ N U (N T)) + ∑ k ∈ Finset.Icc 1 (N T), rr k := by
    rw [Finset.sum_congr rfl hHl, Finset.sum_add_distrib, ← Finset.mul_sum, hlost]
  -- bounds on the potential at 0 and T
  have hΦ : ∀ t, |Fpot η g μ M ς (vA μ N U t) (U t) t| ≤ Cp := fun t =>
    abs_Fpot_le η g μ hη0 hμ M ς t _ _ (fun i hi => (hUfacts t).1 _ (by omega) (by omega))
  have hΦT := abs_le.mp (hΦ T)
  have hΦ0 := abs_le.mp (hΦ 0)
  rw [hHlsum]
  linarith [hpot, hjsum, hint]

end pw

end LostSalesRQ

namespace LostSalesRQ

open MeasureTheory ProbabilityTheory Filter Set Topology

section left
variable {μ : ℝ} {N U : ℝ → ℕ}

/-- The path integrand has the left-state value as its left limit. -/
lemma Hpath_left (η g ap : ℝ) (M : ℕ) (h : PathOK μ N U) (t : ℝ) :
    Tendsto (Hpath η g μ ap M N U) (𝓝[<] t)
      (𝓝 (Psi η g μ ap M (arrT U) (vS μ N U (leftLim N t)) (leftLim U t) (leftLim U (t - μ)) t)) := by
  obtain ⟨s1, hs1, he1⟩ := leftLim_attained h.hN.1 t
  obtain ⟨s2, hs2, he2⟩ := leftLim_attained h.hU.1 t
  obtain ⟨s3, hs3, he3⟩ := leftLim_attained h.hU.1 (t - μ)
  set s0 := max s1 (max s2 (s3 + μ)) with hs0
  have hs0t : s0 < t := max_lt hs1 (max_lt hs2 (by linarith))
  have hev : (Hpath η g μ ap M N U) =ᶠ[𝓝[<] t]
      (Psi η g μ ap M (arrT U) (vS μ N U (leftLim N t)) (leftLim U t) (leftLim U (t - μ))) := by
    filter_upwards [Ioo_mem_nhdsLT hs0t] with s hs
    have h1 : s1 ≤ s := le_trans (le_max_left _ _) hs.1.le
    have h2 : s2 ≤ s := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hs.1.le
    have h3 : s3 + μ ≤ s := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hs.1.le
    unfold Hpath vA
    rw [he1 s h1 hs.2, he2 s h2 hs.2, he3 (s - μ) (by linarith) (by linarith [hs.2])]
  exact (((continuous_Psi η g μ ap M (arrT U) _ _ _).tendsto t).mono_left
    nhdsWithin_le_nhds).congr' hev.symm

lemma Hpath_left_arr (η g ap : ℝ) (M : ℕ) (h : PathOK μ N U) (k : ℕ) :
    Tendsto (Hpath η g μ ap M N U) (𝓝[<] (arrT N k)) (𝓝 (Hlpath η g μ ap M N U k)) :=
  Hpath_left η g ap M h (arrT N k)

lemma Hpath_left_ae (η g ap : ℝ) (M : ℕ) (h : PathOK μ N U) (T : ℝ) :
    ∀ᵐ t ∂volume, t ∈ Ioc 0 T →
      Tendsto (Hpath η g μ ap M N U) (𝓝[<] t) (𝓝 (Hpath η g μ ap M N U t)) := by
  set Z : Set ℝ := epochSet N T ∪ epochSet U T ∪ ((fun s => s + μ) '' epochSet U T) ∪ {μ} with hZ
  have hZf : Z.Finite :=
    (((epochSet_finite h.hN.1 T).union (epochSet_finite h.hU.1 T)).union
      ((epochSet_finite h.hU.1 T).image _)).union (finite_singleton μ)
  have hZ0 : volume Z = 0 := hZf.measure_zero _
  filter_upwards [measure_eq_zero_iff_ae_notMem.mp hZ0] with t htZ htT
  have hlN : leftLim N t = N t := by
    by_contra hne
    exact htZ (Or.inl (Or.inl (Or.inl ⟨htT, lt_of_le_of_ne (leftLim_le_self h.hN.1 t) hne⟩)))
  have hlU : leftLim U t = U t := by
    by_contra hne
    exact htZ (Or.inl (Or.inl (Or.inr ⟨htT, lt_of_le_of_ne (leftLim_le_self h.hU.1 t) hne⟩)))
  have hlUμ : leftLim U (t - μ) = U (t - μ) := by
    rcases lt_trichotomy (t - μ) 0 with hneg | hzero | hpos
    · rw [leftLim_nonpos h.hU.1 h.hU0 hneg.le, h.hU0 _ hneg]
    · exfalso; exact htZ (Or.inr (by simp; linarith))
    · by_contra hne
      exact htZ (Or.inl (Or.inr ⟨t - μ, ⟨⟨hpos, by linarith [htT.2, h.hμ]⟩,
        lt_of_le_of_ne (leftLim_le_self h.hU.1 _) hne⟩, by ring⟩))
  have := Hpath_left η g ap M h t
  rw [hlN, hlU, hlUμ] at this
  exact this

end left

/-- Comparison of the served counts with and without extra initial supply. -/
lemma srec_cmp (av av' i : ℕ → ℕ) (n : ℕ) (hav : ∀ k, 1 ≤ k → k ≤ n → av k = av' k + i k)
    (hi : ∀ k k', 1 ≤ k → k ≤ k' → k' ≤ n → i k ≤ i k') :
    ∀ k, k ≤ n → srec av' k ≤ srec av k ∧ srec av k ≤ srec av' k + (if k = 0 then 0 else i k) := by
  intro k
  induction k with
  | zero => intro _; simp [srec]
  | succ k ih =>
    intro hkn
    obtain ⟨h1, h2⟩ := ih (by omega)
    simp only [srec]
    rw [hav (k + 1) (by omega) hkn]
    have hik : (if k = 0 then 0 else i k) ≤ i (k + 1) := by
      split_ifs with hk
      · exact Nat.zero_le _
      · exact hi k (k + 1) (by omega) (by omega) hkn
    simp only [Nat.add_one_ne_zero, if_false]
    constructor <;> split_ifs <;> omega

/-- Recursion driven by a predicate. -/
noncomputable def srecP (P : ℕ → ℕ → Prop) : ℕ → ℕ
  | 0 => 0
  | k + 1 => srecP P k + @ite _ (P (k + 1) (srecP P k)) (Classical.dec _) 1 0

lemma srecP_eq (P : ℕ → ℕ → Prop) (av : ℕ → ℕ) (n : ℕ)
    (hP : ∀ k, 1 ≤ k → k ≤ n → ∀ s, P k s ↔ s < av k) : ∀ k, k ≤ n → srecP P k = srec av k := by
  intro k
  induction k with
  | zero => intro _; rfl
  | succ k ih =>
    intro hkn
    have e := ih (by omega)
    have hk := hP (k + 1) (by omega) hkn (srec av k)
    show srecP P k + @ite _ (P (k + 1) (srecP P k)) (Classical.dec _) 1 0 =
      srec av k + ite (srec av k < av (k + 1)) 1 0
    by_cases hp : P (k + 1) (srecP P k)
    · have hp' : P (k + 1) (srec av k) := by rw [← e]; exact hp
      rw [if_pos hp, e, if_pos (hk.mp hp')]
    · have hp' : ¬ P (k + 1) (srec av k) := by rw [← e]; exact hp
      rw [if_neg hp, e, if_neg (fun h => hp' (hk.mpr h))]

lemma measurable_sel' {α : Type*} {_ : MeasurableSpace α} {β : Type*} [Countable β]
    [MeasurableSpace β] [MeasurableSingletonClass β] {γ : Type*} [MeasurableSpace γ]
    {G : β → α → γ} (hG : ∀ b, Measurable (G b))
    {K : α → β} (hK : Measurable K) : Measurable (fun x => G (K x) x) :=
  (measurable_from_prod_countable_left (f := fun p : α × β => G p.2 p.1) hG).comp
    (measurable_id.prodMk hK)

lemma measurable_srecP {α : Type*} {m : MeasurableSpace α} (P : α → ℕ → ℕ → Prop)
    (hP : ∀ k s, MeasurableSet {x | P x k s}) (k : ℕ) : Measurable (fun x => srecP (P x) k) := by
  induction k with
  | zero => exact measurable_const
  | succ k ih =>
    simp only [srecP]
    have : (fun x => srecP (P x) k + @ite _ (P x (k + 1) (srecP (P x) k)) (Classical.dec _) 1 0) =
        fun x => (fun s x' => s + @ite _ (P x' (k + 1) s) (Classical.dec _) 1 0) (srecP (P x) k) x :=
      rfl
    rw [this]
    refine measurable_sel' (β := ℕ) (γ := ℕ)
      (G := fun s x' => s + @ite _ (P x' (k + 1) s) (Classical.dec _) 1 0) (fun s => ?_) ih
    refine Measurable.add measurable_const ?_
    exact Measurable.ite (hP (k + 1) s) measurable_const measurable_const

/-- The potential only reads the delivery epochs of committed units. -/
lemma Fpot_congr (η g μ : ℝ) (M : ℕ) (ς ς' : ℕ → ℝ) (a u : ℕ) (t : ℝ)
    (h : ∀ j, 1 ≤ j → j ≤ u → ς j = ς' j) : Fpot η g μ M ς a u t = Fpot η g μ M ς' a u t := by
  unfold Fpot
  apply Finset.sum_congr rfl; intro i hi
  rw [h _ (by omega) (by have := Finset.mem_range.mp hi; omega)]

lemma Psi_congr (η g μ ap : ℝ) (M : ℕ) (ς ς' : ℕ → ℝ) (a u v : ℕ) (t : ℝ)
    (h : ∀ j, 1 ≤ j → j ≤ u → ς j = ς' j) :
    Psi η g μ ap M ς a u v t = Psi η g μ ap M ς' a u v t := by
  unfold Psi; rw [Fpot_congr η g μ M ς ς' _ u t h, Fpot_congr η g μ M ς ς' _ u t h]

lemma measurable_Fpot_coord {α : Type*} {m : MeasurableSpace α} (η g μ : ℝ) (M : ℕ)
    (ς : α → ℕ → ℝ) (hς : ∀ j, Measurable (fun x => ς x j)) (a u : ℕ) (t : ℝ) :
    Measurable (fun x => Fpot η g μ M (ς x) a u t) := by
  unfold Fpot Wt
  refine Finset.measurable_sum _ (fun i _ => ?_)
  exact (continuous_VV η g _).measurable.comp
    (measurable_const.max (((hς _).add_const μ).sub_const t))

lemma measurable_Psi_coord {α : Type*} {m : MeasurableSpace α} (η g μ ap : ℝ) (M : ℕ)
    (ς : α → ℕ → ℝ) (hς : ∀ j, Measurable (fun x => ς x j)) (a u v : ℕ) (t : ℝ) :
    Measurable (fun x => Psi η g μ ap M (ς x) a u v t) := by
  unfold Psi
  apply measurable_const.add
  split_ifs
  · exact (measurable_Fpot_coord η g μ M ς hς _ u t).sub (measurable_Fpot_coord η g μ M ς hς a u t)
  · exact measurable_const

end LostSalesRQ

namespace LostSalesRQ

open MeasureTheory ProbabilityTheory Filter Set Topology

lemma cs_ofReal_max0 (x : ℝ) : ENNReal.ofReal x = ENNReal.ofReal (max x 0) := by
  rcases le_total x 0 with h | h
  · rw [max_eq_right h, ENNReal.ofReal_of_nonpos h, ENNReal.ofReal_zero]
  · rw [max_eq_left h]

lemma ofReal_integral_le {α : Type*} {_ : MeasurableSpace α} {ν : Measure α} {f : α → ℝ}
    (hf : Integrable f ν) : ENNReal.ofReal (∫ x, f x ∂ν) ≤ ∫⁻ x, ENNReal.ofReal (f x) ∂ν := by
  have h1 : ∫ x, f x ∂ν ≤ ∫ x, max (f x) 0 ∂ν :=
    integral_mono hf (hf.pos_part) (fun x => le_max_left _ _)
  calc ENNReal.ofReal (∫ x, f x ∂ν) ≤ ENNReal.ofReal (∫ x, max (f x) 0 ∂ν) :=
        ENNReal.ofReal_le_ofReal h1
    _ = ∫⁻ x, ENNReal.ofReal (max (f x) 0) ∂ν :=
        ofReal_integral_eq_lintegral_ofReal hf.pos_part
          (Eventually.of_forall (fun x => le_max_right _ _))
    _ = ∫⁻ x, ENNReal.ofReal (f x) ∂ν := by
        congr 1; funext x; rw [← cs_ofReal_max0]

section prob
variable (S : DemandSpace 1) (π : Policy S)

lemma Policy.pathOK (μ : ℝ) (hμ : 0 ≤ μ) (ω : S.Ω) :
    PathOK μ (fun s => S.N s ω) (fun s => π.U s ω) :=
  ⟨S.regPath ω, fun s hs => S.N_nonpos ω s hs, ⟨π.U_mono ω, π.U_rcont ω⟩,
    fun s hs => π.U_nonpos ω s hs, hμ⟩

lemma Policy.measurable_U (t : ℝ) : Measurable (π.U t) := (π.U_adapted t).mono (S.𝓕.le t) le_rfl

/-- Truncated order epochs, adapted at time t. -/
noncomputable def stt (t : ℝ) (ω : S.Ω) (j : ℕ) : ℝ :=
  if 1 ≤ j ∧ j ≤ π.U t ω then arrT (fun s => π.U s ω) j else t

lemma measurable_stt (t : ℝ) (j : ℕ) : Measurable[S.𝓕 t] (fun ω => stt S π t ω j) := by
  by_cases hj : 1 ≤ j
  · apply measurable_of_Iic
    intro r
    by_cases hr : t ≤ r
    · convert MeasurableSet.univ
      ext ω; simp only [mem_preimage, mem_Iic, mem_univ, iff_true]
      unfold stt; split_ifs with h
      · exact le_trans ((arrT_spec' ⟨π.U_mono ω, π.U_rcont ω⟩ (fun s hs => π.U_nonpos ω s hs)
          h.1 h.2 t).mp h.2) hr
      · exact hr
    · push Not at hr
      have : (fun ω => stt S π t ω j) ⁻¹' Iic r = {ω | j ≤ π.U r ω} := by
        ext ω; simp only [mem_preimage, mem_Iic, mem_ofPred_eq]
        unfold stt
        constructor
        · intro h
          split_ifs at h with h'
          · exact (arrT_spec' ⟨π.U_mono ω, π.U_rcont ω⟩ (fun s hs => π.U_nonpos ω s hs)
              h'.1 h'.2 r).mpr h
          · linarith
        · intro h
          have hjt : j ≤ π.U t ω := le_trans h (π.U_mono ω hr.le)
          rw [if_pos ⟨hj, hjt⟩]
          exact (arrT_spec' ⟨π.U_mono ω, π.U_rcont ω⟩ (fun s hs => π.U_nonpos ω s hs)
            hj hjt r).mp h
      rw [this]
      exact S.𝓕.mono hr.le _ ((π.U_adapted r) (MeasurableSet.of_discrete))
  · have : (fun ω => stt S π t ω j) = fun _ => t := by
      funext ω; unfold stt; rw [if_neg (fun h => hj h.1)]
    rw [this]; exact measurable_const

/-- The predicate characterizing service in the empty system through countably many values. -/
def servPred (μ t : ℝ) (ω : S.Ω) (k s : ℕ) : Prop :=
  ∃ q : ℚ, (q : ℝ) + μ < t ∧ s < π.U q ω ∧ S.N (q + μ) ω < k

lemma servPred_iff (μ : ℝ) (hμ : 0 ≤ μ) (t : ℝ) (ω : S.Ω) {k : ℕ} (hk : 1 ≤ k)
    (hkt : k ≤ S.N t ω) (s : ℕ) :
    servPred S π μ t ω k s ↔ s < vAv μ (fun s => S.N s ω) (fun s => π.U s ω) k := by
  have h := π.pathOK S μ hμ ω
  unfold servPred vAv
  constructor
  · rintro ⟨q, hq1, hq2, hq3⟩
    have : ¬ arrT (fun s => S.N s ω) k ≤ q + μ := fun hc =>
      absurd ((arrT_spec h.hN h.hN0 hk hkt _).mpr hc) (not_le.mpr hq3)
    push Not at this
    exact lt_of_lt_of_le hq2 (le_leftLim h.hU.1 (by linarith))
  · intro hs
    obtain ⟨r, hr, hsr⟩ := (lt_leftLim_iff h.hU.1 _ s).mp hs
    obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn hr
    have hσt := arrT_le h.hN h.hN0 hk hkt
    refine ⟨q, by linarith, lt_of_lt_of_le hsr (h.hU.1 hq1.le), ?_⟩
    by_contra hc; push Not at hc
    have := (arrT_spec h.hN h.hN0 hk hkt _).mp hc
    linarith

lemma vA_eq_srecP (μ : ℝ) (hμ : 0 ≤ μ) (t : ℝ) (ω : S.Ω) :
    vA μ (fun s => S.N s ω) (fun s => π.U s ω) t = srecP (servPred S π μ t ω) (S.N t ω) := by
  unfold vA vS
  exact (srecP_eq _ _ (S.N t ω) (fun k hk hkt s => servPred_iff S π μ hμ t ω hk hkt s)
    (S.N t ω) le_rfl).symm

lemma measurable_vA (μ : ℝ) (hμ : 0 ≤ μ) (t : ℝ) :
    Measurable[S.𝓕 t] (fun ω => vA μ (fun s => S.N s ω) (fun s => π.U s ω) t) := by
  simp_rw [vA_eq_srecP S π μ hμ t]
  have hP : ∀ k s, MeasurableSet[S.𝓕 t] {ω | servPred S π μ t ω k s} := by
    intro k s
    have : {ω | servPred S π μ t ω k s} = ⋃ q : ℚ,
        (if (q : ℝ) + μ < t then {ω | s < π.U q ω} ∩ {ω | S.N (q + μ) ω < k} else ∅) := by
      ext ω; simp only [servPred, mem_ofPred_eq, mem_iUnion]
      constructor
      · rintro ⟨q, h1, h2, h3⟩; exact ⟨q, by rw [if_pos h1]; exact ⟨h2, h3⟩⟩
      · rintro ⟨q, hq⟩
        split_ifs at hq with h1
        · exact ⟨q, h1, hq.1, hq.2⟩
        · exact absurd hq (notMem_empty ω)
    rw [this]
    refine MeasurableSet.iUnion (fun q => ?_)
    split_ifs with h1
    · exact (S.𝓕.mono (show (q : ℝ) ≤ t by linarith) _
        ((π.U_adapted q) (MeasurableSet.of_discrete (s := {n : ℕ | s < n})))).inter
        (S.𝓕.mono h1.le _ ((S.N_adapted ((q : ℝ) + μ))
          (MeasurableSet.of_discrete (s := {n : ℕ | n < k}))))
    · exact @MeasurableSet.empty _ (S.𝓕 t)
  exact measurable_sel' (β := ℕ) (γ := ℕ) (G := fun n ω => srecP (servPred S π μ t ω) n)
    (fun n => measurable_srecP (m := S.𝓕 t) _ hP n) (S.N_adapted t)

/-- The integrand of the compensation argument. -/
noncomputable def Hproc (η g μ ap : ℝ) (M : ℕ) (t : ℝ) (ω : S.Ω) : ℝ :=
  Hpath η g μ ap M (fun s => S.N s ω) (fun s => π.U s ω) t

lemma measurable_Hproc (η g μ ap : ℝ) (M : ℕ) (hμ : 0 ≤ μ) (t : ℝ) :
    Measurable[S.𝓕 t] (Hproc S π η g μ ap M t) := by
  have heq : Hproc S π η g μ ap M t = fun ω => Psi η g μ ap M (stt S π t ω)
      (vA μ (fun s => S.N s ω) (fun s => π.U s ω) t) (π.U t ω) (π.U (t - μ) ω) t := by
    funext ω
    unfold Hproc Hpath
    apply Psi_congr
    intro j hj hjt
    unfold stt; rw [if_pos ⟨hj, hjt⟩]
  rw [heq]
  have hK : Measurable[S.𝓕 t] (fun ω => (vA μ (fun s => S.N s ω) (fun s => π.U s ω) t,
      π.U t ω, π.U (t - μ) ω)) :=
    (measurable_vA S π μ hμ t).prodMk ((π.U_adapted t).prodMk
      ((π.U_adapted (t - μ)).mono (S.𝓕.mono (by linarith)) le_rfl))
  exact measurable_sel (β := ℕ × ℕ × ℕ)
    (G := fun b ω => Psi η g μ ap M (stt S π t ω) b.1 b.2.1 b.2.2 t)
    (fun b => measurable_Psi_coord (m := S.𝓕 t) η g μ ap M (stt S π t)
      (measurable_stt S π t) _ _ _ t) hK

end prob

end LostSalesRQ

namespace LostSalesRQ

open MeasureTheory ProbabilityTheory Filter Set Topology

section final
variable (S : DemandSpace 1) (π : Policy S)

/-- Realized holding plus lost-sales cost of the empty-start copy. -/
noncomputable def vcost (μ ap T : ℝ) (ω : S.Ω) : ℝ :=
  (∫ t in (0:ℝ)..T, ((π.U (t - μ) ω - vA μ (fun s => S.N s ω) (fun s => π.U s ω) t : ℕ) : ℝ)) +
    ap * ((S.N T ω : ℝ) - vS μ (fun s => S.N s ω) (fun s => π.U s ω) (S.N T ω))

theorem expected_vcost (η g μ ap : ℝ) (M : ℕ) (hμ : 0 ≤ μ) {T : ℝ} (hT : 0 < T)
    (hη : 1 ≤ η) (hg0 : 0 ≤ g) (hgB : g ≤ rankBound μ η) (hgD : g ≤ ap - agingRateSup μ η)
    (hM1 : 1 ≤ M) (hMg : μ + g ≤ M) (hap : 0 ≤ ap) :
    ENNReal.ofReal (g * T - 2 * (M * (M + μ + η + |g|))) ≤
      ∫⁻ ω, ENNReal.ofReal (vcost S π μ ap T ω) ∂S.ν := by
  have hη0 : 0 ≤ η := by linarith
  set Cp := (M : ℝ) * (M + μ + η + |g|) with hCp
  set H := Hproc S π η g μ ap M with hH
  set Hl : ℕ → S.Ω → ℝ := fun k ω =>
    Hlpath η g μ ap M (fun s => S.N s ω) (fun s => π.U s ω) k with hHl
  have hcomp := compensation S T hT H (ap + 2 * Cp)
    (fun t _ => measurable_Hproc S π η g μ ap M hμ t)
    (fun t ω => abs_Psi_le η g μ ap hη0 hμ hap M _ _ _ _ t
      (fun j hj hju => ((unit_facts (π.pathOK S μ hμ ω)) t).1 j hj hju))
    Hl (fun ω k _ _ => Hpath_left_arr η g ap M (π.pathOK S μ hμ ω) k)
    (fun ω => Hpath_left_ae η g ap M (π.pathOK S μ hμ ω) T)
  obtain ⟨hi1, hi2, heq⟩ := hcomp
  set Z : S.Ω → ℝ := fun ω => (∑ k ∈ Finset.Icc 1 (S.N T ω), Hl k ω) -
    ∫ t in (0:ℝ)..T, H t ω with hZ
  have hZi : Integrable Z S.ν := hi1.sub hi2
  have hZ0 : ∫ ω, Z ω ∂S.ν = 0 := by
    simp only [hZ]; rw [integral_sub hi1 hi2, heq, sub_self]
  have hpt : ∀ᵐ ω ∂S.ν, g * T - 2 * Cp + Z ω ≤ vcost S π μ ap T ω := by
    filter_upwards [ae_noBatch S T hT] with ω hω
    exact (pathwise_bound η g μ ap M (π.pathOK S μ hμ ω) hT hω hη hg0 hgB hgD hM1 hMg hap).2.2
  calc ENNReal.ofReal (g * T - 2 * Cp)
      = ENNReal.ofReal (∫ ω, (g * T - 2 * Cp + Z ω) ∂S.ν) := by
        rw [integral_add (integrable_const _) hZi, hZ0, add_zero, integral_const, smul_eq_mul,
          probReal_univ, one_mul]
    _ ≤ ∫⁻ ω, ENNReal.ofReal (g * T - 2 * Cp + Z ω) ∂S.ν :=
        ofReal_integral_le ((integrable_const _).add hZi)
    _ ≤ ∫⁻ ω, ENNReal.ofReal (vcost S π μ ap T ω) ∂S.ν :=
        lintegral_mono_ae (hpt.mono (fun ω h => ENNReal.ofReal_le_ofReal h))

end final

end LostSalesRQ

namespace LostSalesRQ

open MeasureTheory ProbabilityTheory Filter Set Topology

lemma lintegral_Icc_natCast {f : ℝ → ℕ} (hf : Measurable f) {T C : ℝ} (hT : 0 ≤ T)
    (hb : ∀ t ∈ Icc 0 T, (f t : ℝ) ≤ C) :
    ∫⁻ t in Icc 0 T, (f t : ENNReal) = ENNReal.ofReal (∫ t in (0:ℝ)..T, (f t : ℝ)) := by
  have hm : Measurable (fun t => (f t : ℝ)) := (measurable_from_nat (f := fun n : ℕ => (n : ℝ))).comp hf
  have hint : IntegrableOn (fun t => (f t : ℝ)) (Icc 0 T) := by
    refine Measure.integrableOn_of_bounded (M := C) (by simp) hm.aestronglyMeasurable ?_
    refine ae_restrict_of_forall_mem measurableSet_Icc (fun t ht => ?_)
    rw [Real.norm_eq_abs, Nat.abs_cast]; exact hb t ht
  rw [intervalIntegral.integral_of_le hT, ← integral_Icc_eq_integral_Ioc,
    ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall (fun t => Nat.cast_nonneg _))]
  congr 1; funext t; rw [ENNReal.ofReal_natCast]

section final2
variable (S : DemandSpace 1) (π : Policy S)

theorem vcost_le_cost (μ a T : ℝ) (hμ : 0 ≤ μ) (hT : 0 ≤ T) (ha : 0 ≤ a) (ω : S.Ω) :
    ENNReal.ofReal (vcost S π μ a T ω) ≤
      π.horizonCost μ 1 a 0 T ω + ENNReal.ofReal a * ((min (π.init T ω) (S.N T ω) : ℕ) : ENNReal) := by
  have h := π.pathOK S μ hμ ω
  set N : ℝ → ℕ := fun s => S.N s ω with hN
  set U : ℝ → ℕ := fun s => π.U s ω with hU
  set I0 : ℝ → ℕ := fun s => π.init s ω with hI0
  have hI0m : Monotone I0 := π.init_mono ω
  set ic : ℕ → ℕ := fun k => leftLim I0 (arrT N k) with hic
  have hcust : ∀ k, custAvail μ I0 U N k = vAv μ N U k + ic k := fun k => by
    unfold custAvail vAv; rw [hic]; ring
  have hcmp := srec_cmp (custAvail μ I0 U N) (vAv μ N U) ic (N T)
    (fun k _ _ => hcust k)
    (fun k k' hk hkk hk' => leftLim_mono hI0m
      (arrT_mono' h.hN (fun s hs => h.hN0 s hs.le) hk hkk hk'))
  have hserved : ∀ t, π.served μ t ω = srec (custAvail μ I0 U N) (N t) := fun t =>
    servedPath_srec μ I0 U N h.hN h.hN0 t
  have hic_le : ∀ t, 0 ≤ t → N t ≤ N T → (if N t = 0 then 0 else ic (N t)) ≤ I0 t := by
    intro t ht _
    split_ifs with h0
    · exact Nat.zero_le _
    · have hpos : 1 ≤ N t := Nat.one_le_iff_ne_zero.mpr h0
      have hσ := arrT_le h.hN h.hN0 hpos (le_refl (N t))
      exact le_trans (leftLim_le_self hI0m _) (hI0m hσ)
  -- holding
  have hhold : ∀ t ∈ Icc 0 T, U (t - μ) - vA μ N U t ≤ π.onHand μ t ω := by
    intro t ht
    have hNt : N t ≤ N T := h.hN.1 ht.2
    obtain ⟨_, h2⟩ := hcmp (N t) hNt
    have h3 := hic_le t ht.1 hNt
    unfold Policy.onHand delivered
    rw [hserved t]
    unfold vA vS
    simp only [hN, hU, hI0] at h2 h3 ⊢
    omega
  -- lost sales
  have hlost : S.N T ω - vS μ N U (S.N T ω) ≤ π.lost μ T ω + min (π.init T ω) (S.N T ω) := by
    obtain ⟨h1, h2⟩ := hcmp (N T) le_rfl
    have h3 := hic_le T hT le_rfl
    have h4 := srec_le (custAvail μ I0 U N) (N T)
    unfold Policy.lost
    rw [hserved T]
    unfold vS
    simp only [hN, hU, hI0] at h1 h2 h3 h4 ⊢
    omega
  -- assemble
  have hvS : vS μ N U (S.N T ω) ≤ S.N T ω := srec_le _ _
  have hIm : Measurable (fun t => U (t - μ) - vA μ N U t) :=
    (h.hU.1.measurable.comp (measurable_id.sub_const μ)).sub
      ((measurable_from_nat (f := vS μ N U)).comp h.hN.1.measurable)
  have hconv := lintegral_Icc_natCast hIm hT (C := U T) (fun t ht => by
    have : U (t - μ) - vA μ N U t ≤ U T := le_trans (Nat.sub_le _ _) (h.hU.1 (by linarith [ht.2]))
    exact_mod_cast this)
  unfold vcost Policy.horizonCost
  simp only [ENNReal.ofReal_one, one_mul, ENNReal.ofReal_zero, zero_mul, add_zero]
  calc ENNReal.ofReal ((∫ t in (0:ℝ)..T, ((U (t - μ) - vA μ N U t : ℕ) : ℝ)) +
        a * ((S.N T ω : ℝ) - vS μ N U (S.N T ω)))
      ≤ ENNReal.ofReal (∫ t in (0:ℝ)..T, ((U (t - μ) - vA μ N U t : ℕ) : ℝ)) +
        ENNReal.ofReal (a * ((S.N T ω : ℝ) - vS μ N U (S.N T ω))) := ENNReal.ofReal_add_le
    _ = (∫⁻ t in Icc 0 T, ((U (t - μ) - vA μ N U t : ℕ) : ENNReal)) +
        ENNReal.ofReal a * ((S.N T ω - vS μ N U (S.N T ω) : ℕ) : ENNReal) := by
        rw [← hconv, ENNReal.ofReal_mul ha, ← Nat.cast_sub hvS, ENNReal.ofReal_natCast]
    _ ≤ (∫⁻ t in Icc 0 T, (π.onHand μ t ω : ENNReal)) +
        ENNReal.ofReal a * ((π.lost μ T ω : ENNReal) + ((min (π.init T ω) (S.N T ω) : ℕ) : ENNReal)) := by
        refine add_le_add (setLIntegral_mono' measurableSet_Icc (fun t ht => ?_)) ?_
        · exact_mod_cast hhold t ht
        · gcongr; exact_mod_cast hlost
    _ = _ := by ring

end final2

end LostSalesRQ

namespace LostSalesRQ

open MeasureTheory ProbabilityTheory Filter Set Topology

section final3
variable (S : DemandSpace 1) (π : Policy S)

/-- Paths whose initial supply exceeds n at some time. -/
def bigInit (n : ℕ) : Set S.Ω := {ω | ∃ m : ℕ, n < π.init m ω}

lemma measurableSet_bigInit (n : ℕ) : MeasurableSet[S.𝓕 0] (bigInit S π n) := by
  have : bigInit S π n = ⋃ m : ℕ, {ω | n < π.init m ω} := by ext ω; simp [bigInit]
  rw [this]
  exact MeasurableSet.iUnion (fun m => (π.init_meas m) (MeasurableSet.of_discrete (s := {k : ℕ | n < k})))

lemma tendsto_bigInit : Tendsto (fun n => S.ν (bigInit S π n)) atTop (𝓝 0) := by
  have hanti : Antitone (bigInit S π) := by
    intro n n' hnn ω hω
    obtain ⟨m, hm⟩ := hω; exact ⟨m, lt_of_le_of_lt hnn hm⟩
  have hempty : (⋂ n, bigInit S π n) = ∅ := by
    ext ω
    simp only [mem_iInter, mem_empty_iff_false, iff_false, not_forall]
    obtain ⟨c, hc⟩ := π.init_bdd ω
    refine ⟨c, ?_⟩
    rintro ⟨m, hm⟩; have := hc m; omega
  have := tendsto_measure_iInter_atTop (μ := S.ν)
    (fun n => (S.𝓕.le 0 _ (measurableSet_bigInit S π n)).nullMeasurableSet) hanti
    ⟨0, measure_ne_top _ _⟩
  rwa [hempty, measure_empty] at this

lemma init_tail (T : ℝ) (hT : 0 < T) (n : ℕ) :
    ∫⁻ ω, ((min (π.init T ω) (S.N T ω) : ℕ) : ENNReal) ∂S.ν ≤
      ENNReal.ofReal (n + T * (S.ν (bigInit S π n)).toReal) := by
  set Y : S.Ω → ℝ := (bigInit S π n).indicator 1 with hY
  have hYm : Measurable[S.𝓕 0] Y := by
    rw [hY]
    exact Measurable.indicator (m := S.𝓕 0) (measurable_const (a := (1 : ℝ)))
      (measurableSet_bigInit S π n)
  have hpt : ∀ ω, ((min (π.init T ω) (S.N T ω) : ℕ) : ℝ) ≤ n + Y ω * (S.inc 0 T ω : ℝ) := by
    intro ω
    have hinc : S.inc 0 T ω = S.N T ω := by
      unfold DemandSpace.inc; rw [S.N_nonpos ω 0 le_rfl, Nat.sub_zero]
    rw [hinc]
    by_cases hb : ω ∈ bigInit S π n
    · rw [hY, indicator_of_mem hb, Pi.one_apply, one_mul]
      have : min (π.init T ω) (S.N T ω) ≤ S.N T ω := min_le_right _ _
      have : ((min (π.init T ω) (S.N T ω) : ℕ) : ℝ) ≤ S.N T ω := by exact_mod_cast this
      linarith [Nat.cast_nonneg (α := ℝ) n]
    · rw [hY, indicator_of_notMem hb, zero_mul, add_zero]
      have : π.init T ω ≤ n := by
        by_contra hc; push Not at hc
        exact hb ⟨⌈T⌉₊, lt_of_lt_of_le hc (π.init_mono ω (Nat.le_ceil T))⟩
      exact_mod_cast le_trans (min_le_left _ _) this
  have hYb : ∀ ω, ‖Y ω‖ ≤ 1 := fun ω => by
    rw [hY]; by_cases hb : ω ∈ bigInit S π n
    · rw [indicator_of_mem hb]; simp
    · rw [indicator_of_notMem hb]; simp
  have hint : Integrable (fun ω => (n : ℝ) + Y ω * (S.inc 0 T ω : ℝ)) S.ν :=
    (integrable_const _).add ((S.integrable_inc le_rfl hT.le (by linarith)).bdd_mul
      (hYm.mono (S.𝓕.le 0) le_rfl).aestronglyMeasurable (Eventually.of_forall hYb))
  have hval : ∫ ω, ((n : ℝ) + Y ω * (S.inc 0 T ω : ℝ)) ∂S.ν = n + T * (S.ν (bigInit S π n)).toReal := by
    rw [integral_add (integrable_const _) ((S.integrable_inc le_rfl hT.le (by linarith)).bdd_mul
      (hYm.mono (S.𝓕.le 0) le_rfl).aestronglyMeasurable (Eventually.of_forall hYb)),
      S.integral_mul_inc le_rfl hT.le (by linarith) Y hYm, integral_const, smul_eq_mul,
      probReal_univ, one_mul]
    rw [hY, integral_indicator_one (S.𝓕.le 0 _ (measurableSet_bigInit S π n))]
    simp only [Measure.real]; ring
  rw [← hval, ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall (fun ω => by
    have : 0 ≤ Y ω := by rw [hY]; exact indicator_nonneg (fun _ _ => zero_le_one) ω
    positivity))]
  refine lintegral_mono (fun ω => ?_)
  dsimp only
  rw [← ENNReal.ofReal_natCast]
  exact ENNReal.ofReal_le_ofReal (hpt ω)

end final3

end LostSalesRQ

namespace LostSalesRQ

open MeasureTheory ProbabilityTheory Filter Set Topology

theorem cs_policy_bound (S : DemandSpace 1) (π : Policy S) (μ a η : ℝ) (hμ : 0 ≤ μ)
    (ha : 0 ≤ a) (hη : 1 ≤ η) :
    ENNReal.ofReal (min (rankBound μ η) (a - agingRateSup μ η)) ≤ π.avgCost μ 1 a 0 := by
  set g := min (rankBound μ η) (a - agingRateSup μ η) with hg
  by_cases hg0 : g ≤ 0
  · rw [ENNReal.ofReal_of_nonpos hg0]; exact zero_le
  push Not at hg0
  have hgB : g ≤ rankBound μ η := min_le_left _ _
  have hgD : g ≤ a - agingRateSup μ η := min_le_right _ _
  set M : ℕ := ⌈μ + g⌉₊ + 1 with hM
  have hM1 : 1 ≤ M := by omega
  have hMg : μ + g ≤ M := by
    have := Nat.le_ceil (μ + g); rw [hM]; push_cast; linarith
  set Cp := (M : ℝ) * (M + μ + η + |g|) with hCp
  have hCp0 : 0 ≤ Cp := by have := abs_nonneg g; positivity
  have hmeasmin : ∀ T, Measurable (fun ω => ((min (π.init T ω) (S.N T ω) : ℕ) : ENNReal)) := by
    intro T
    have h1 : Measurable (π.init T) := (π.init_meas T).mono (S.𝓕.le 0) le_rfl
    exact (measurable_of_countable (fun p : ℕ × ℕ => ((min p.1 p.2 : ℕ) : ENNReal))).comp
      (h1.prodMk (S.measurable_N T))
  have hkey : ∀ T, 0 < T → ENNReal.ofReal (g * T - 2 * Cp) ≤
      (∫⁻ ω, π.horizonCost μ 1 a 0 T ω ∂S.ν) +
        ENNReal.ofReal a * ∫⁻ ω, ((min (π.init T ω) (S.N T ω) : ℕ) : ENNReal) ∂S.ν := by
    intro T hT
    calc ENNReal.ofReal (g * T - 2 * Cp)
        ≤ ∫⁻ ω, ENNReal.ofReal (vcost S π μ a T ω) ∂S.ν :=
          expected_vcost S π η g μ a M hμ hT hη hg0.le hgB hgD hM1 hMg ha
      _ ≤ ∫⁻ ω, (π.horizonCost μ 1 a 0 T ω +
            ENNReal.ofReal a * ((min (π.init T ω) (S.N T ω) : ℕ) : ENNReal)) ∂S.ν :=
          lintegral_mono (fun ω => vcost_le_cost S π μ a T hμ hT.le ha ω)
      _ = _ := by
          rw [lintegral_add_right _ ((hmeasmin T).const_mul _), lintegral_const_mul _ (hmeasmin T)]
  have htail := tendsto_bigInit S π
  have hε : ∀ ε, 0 < ε → ε < g → ENNReal.ofReal (g - ε) ≤ π.avgCost μ 1 a 0 := by
    intro ε hε hεg
    have hev : ∀ᶠ n in atTop, S.ν (bigInit S π n) < ENNReal.ofReal (ε / (3 * (a + 1))) :=
      (tendsto_order.1 htail).2 _ (ENNReal.ofReal_pos.mpr (by positivity))
    obtain ⟨n0, hn0⟩ := hev.exists
    set p := (S.ν (bigInit S π n0)).toReal with hp
    have hp0 : 0 ≤ p := ENNReal.toReal_nonneg
    have hap : a * p ≤ ε / 3 := by
      have h1 : p < ε / (3 * (a + 1)) := ENNReal.toReal_lt_of_lt_ofReal hn0
      have h2 : (a + 1) * p ≤ ε / 3 := by
        have := mul_le_mul_of_nonneg_left h1.le (show (0:ℝ) ≤ a + 1 by linarith)
        calc (a + 1) * p ≤ (a + 1) * (ε / (3 * (a + 1))) := this
          _ = ε / 3 := by field_simp
      nlinarith
    set T0 := max 1 (3 * (2 * Cp + a * n0) / ε) with hT0
    have hevT : ∀ᶠ T in atTop, ENNReal.ofReal (g - ε) ≤
        (∫⁻ ω, π.horizonCost μ 1 a 0 T ω ∂S.ν) / ENNReal.ofReal T := by
      filter_upwards [eventually_ge_atTop T0] with T hT
      have hT1 : 1 ≤ T := le_trans (le_max_left _ _) hT
      have hTpos : 0 < T := by linarith
      have hk := hkey T hTpos
      have hm := init_tail S π T hTpos n0
      set X := ∫⁻ ω, π.horizonCost μ 1 a 0 T ω ∂S.ν with hX
      rw [ENNReal.le_div_iff_mul_le (Or.inl (by simp; linarith)) (Or.inl ENNReal.ofReal_ne_top)]
      by_cases hXt : X = ⊤
      · rw [hXt]; exact le_top
      · have h1 : ENNReal.ofReal (g * T - 2 * Cp) ≤ X + ENNReal.ofReal (a * (n0 + T * p)) := by
          calc ENNReal.ofReal (g * T - 2 * Cp)
              ≤ X + ENNReal.ofReal a *
                  ∫⁻ ω, ((min (π.init T ω) (S.N T ω) : ℕ) : ENNReal) ∂S.ν := hk
            _ ≤ X + ENNReal.ofReal a * ENNReal.ofReal (n0 + T * p) := by gcongr
            _ = X + ENNReal.ofReal (a * (n0 + T * p)) := by rw [ENNReal.ofReal_mul ha]
        have h2 : g * T - 2 * Cp ≤ X.toReal + a * (n0 + T * p) := by
          have := (ENNReal.ofReal_le_iff_le_toReal
            (ENNReal.add_ne_top.mpr ⟨hXt, ENNReal.ofReal_ne_top⟩)).mp h1
          rwa [ENNReal.toReal_add hXt ENNReal.ofReal_ne_top,
            ENNReal.toReal_ofReal (by positivity)] at this
        have h3 : 2 * Cp + a * n0 ≤ ε * T / 3 := by
          have h5 := le_trans (le_max_right 1 (3 * (2 * Cp + a * n0) / ε)) hT
          rw [div_le_iff₀ hε] at h5; linarith
        have h4 : (g - ε) * T ≤ X.toReal := by nlinarith
        rw [← ENNReal.ofReal_mul (by linarith), ← ENNReal.ofReal_toReal hXt]
        exact ENNReal.ofReal_le_ofReal h4
    exact le_limsup_of_frequently_le' hevT.frequently
  -- let ε → 0
  have hlim : Tendsto (fun k : ℕ => ENNReal.ofReal (g - g / ((k : ℝ) + 2))) atTop
      (𝓝 (ENNReal.ofReal g)) := by
    apply ENNReal.tendsto_ofReal
    have h1 : Tendsto (fun k : ℕ => g / ((k : ℝ) + 2)) atTop (𝓝 0) := by
      have := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul g
      rw [mul_zero] at this
      refine squeeze_zero (fun k => by positivity) (fun k => ?_) this
      rw [div_eq_mul_one_div]
      apply mul_le_mul_of_nonneg_left _ hg0.le
      apply one_div_le_one_div_of_le (by positivity); linarith
    have := (tendsto_const_nhds (x := g)).sub h1
    rwa [sub_zero] at this
  exact le_of_tendsto' hlim (fun k => hε _ (by positivity) (by
    have : (0 : ℝ) < (k : ℝ) + 2 := by positivity
    rw [div_lt_iff₀ this]; nlinarith))

theorem committed_supply_lower_bound' (μ a η : ℝ) (hμ : 0 ≤ μ) (ha : 0 ≤ a) (hη : 1 ≤ η) :
    ENNReal.ofReal (min (rankBound μ η) (a - agingRateSup μ η)) ≤ OPTk μ a 0 := by
  unfold OPTk OPT
  exact le_iInf₂ (fun S π => cs_policy_bound S π μ a η hμ ha hη)

end LostSalesRQ


namespace LostSalesRQ

open MeasureTheory ProbabilityTheory Filter Set Topology

/-- Service-credit potential of on-hand stock n: minus the credits (b - θ i)^+, i = 1..n. -/
noncomputable def Fp (b θ : ℝ) (n : ℕ) : ℝ := -∑ i ∈ Finset.range n, max (b - θ * ((i : ℝ) + 1)) 0

lemma Fp_succ (b θ : ℝ) (n : ℕ) : Fp b θ (n + 1) = Fp b θ n - max (b - θ * ((n : ℝ) + 1)) 0 := by
  unfold Fp; rw [Finset.sum_range_succ]; ring

lemma Fp_nonpos (b θ : ℝ) (n : ℕ) : Fp b θ n ≤ 0 := by
  unfold Fp; simp only [neg_nonpos]
  exact Finset.sum_nonneg (fun i _ => le_max_right _ _)

lemma Fp_ge (b θ : ℝ) (hθ : 0 < θ) (n : ℕ) : -(b ^ 2 / (2 * θ)) ≤ Fp b θ n := by
  have key : ∀ n : ℕ, (∑ i ∈ Finset.range n, max (b - θ * ((i : ℝ) + 1)) 0) +
      (max (b - θ * n) 0) ^ 2 / (2 * θ) ≤ b ^ 2 / (2 * θ) := by
    intro n
    induction n with
    | zero =>
      simp only [Finset.range_zero, Finset.sum_empty, zero_add, Nat.cast_zero, mul_zero, sub_zero]
      rcases le_total b 0 with h | h
      · rw [max_eq_right h]; have : (0:ℝ) ≤ b ^ 2 / (2 * θ) := by positivity
        simpa using this
      · rw [max_eq_left h]
    | succ n ih =>
      rw [Finset.sum_range_succ]
      push_cast
      set x := max (b - θ * n) 0 with hx
      set y := max (b - θ * ((n : ℝ) + 1)) 0 with hy
      have hstep : y + y ^ 2 / (2 * θ) ≤ x ^ 2 / (2 * θ) := by
        rcases le_total (b - θ * ((n : ℝ) + 1)) 0 with h | h
        · rw [hy, max_eq_right h]; simp; positivity
        · have hx' : x = y + θ := by
            rw [hx, hy, max_eq_left h, max_eq_left (by nlinarith)]; ring
          rw [hx']
          have : (y + θ) ^ 2 / (2 * θ) = y ^ 2 / (2 * θ) + y + θ / 2 := by field_simp; ring
          rw [this]; linarith
      linarith
  have := key n
  have h0 : 0 ≤ (max (b - θ * n) 0) ^ 2 / (2 * θ) := by positivity
  unfold Fp; linarith

/-- Left limit of a delayed path. -/
lemma leftLim_shift (U : ℝ → ℕ) (μ t : ℝ) :
    leftLim (fun s => U (s - μ)) t = leftLim U (t - μ) := by
  unfold leftLim
  congr 1
  ext n; simp only [mem_image, mem_Iio]
  constructor
  · rintro ⟨s, hs, rfl⟩; exact ⟨s - μ, by linarith, rfl⟩
  · rintro ⟨s, hs, rfl⟩; exact ⟨s + μ, by linarith, by simp⟩

lemma regPath_shift {U : ℝ → ℕ} (hU : RegPath U) (μ : ℝ) : RegPath (fun s => U (s - μ)) := by
  refine ⟨fun a b hab => hU.1 (by linarith), fun t => ?_⟩
  obtain ⟨δ, hδ, hc⟩ := hU.2 (t - μ)
  exact ⟨δ, hδ, fun s h1 h2 => hc (s - μ) (by linarith) (by linarith)⟩

section scpath
variable {μ : ℝ} {N U : ℝ → ℕ}

/-- A state functional of (served, delivered) along the path. -/
noncomputable def Gpath (G : ℕ → ℕ → ℝ) (μ : ℝ) (N U : ℝ → ℕ) (t : ℝ) : ℝ :=
  G (vA μ N U t) (U (t - μ))

lemma Gpath_left (G : ℕ → ℕ → ℝ) (h : PathOK μ N U) (t : ℝ) :
    Tendsto (Gpath G μ N U) (𝓝[<] t) (𝓝 (G (vS μ N U (leftLim N t)) (leftLim U (t - μ)))) := by
  obtain ⟨s1, hs1, he1⟩ := leftLim_attained h.hN.1 t
  obtain ⟨s3, hs3, he3⟩ := leftLim_attained h.hU.1 (t - μ)
  set s0 := max s1 (s3 + μ) with hs0
  have hs0t : s0 < t := max_lt hs1 (by linarith)
  apply tendsto_const_nhds.congr'
  filter_upwards [Ioo_mem_nhdsLT hs0t] with s hs
  have h1 : s1 ≤ s := le_trans (le_max_left _ _) hs.1.le
  have h3 : s3 + μ ≤ s := le_trans (le_max_right _ _) hs.1.le
  unfold Gpath vA
  rw [he1 s h1 hs.2, he3 (s - μ) (by linarith) (by linarith [hs.2])]

lemma Gpath_left_ae (G : ℕ → ℕ → ℝ) (h : PathOK μ N U) (T : ℝ) :
    ∀ᵐ t ∂volume, t ∈ Ioc 0 T → Tendsto (Gpath G μ N U) (𝓝[<] t) (𝓝 (Gpath G μ N U t)) := by
  set Z : Set ℝ := epochSet N T ∪ ((fun s => s + μ) '' epochSet U T) ∪ {μ} with hZ
  have hZf : Z.Finite :=
    ((epochSet_finite h.hN.1 T).union ((epochSet_finite h.hU.1 T).image _)).union
      (finite_singleton μ)
  filter_upwards [measure_eq_zero_iff_ae_notMem.mp (hZf.measure_zero _)] with t htZ htT
  have hlN : leftLim N t = N t := by
    by_contra hne
    exact htZ (Or.inl (Or.inl ⟨htT, lt_of_le_of_ne (leftLim_le_self h.hN.1 t) hne⟩))
  have hlUμ : leftLim U (t - μ) = U (t - μ) := by
    rcases lt_trichotomy (t - μ) 0 with hneg | hzero | hpos
    · rw [leftLim_nonpos h.hU.1 h.hU0 hneg.le, h.hU0 _ hneg]
    · exfalso; exact htZ (Or.inr (by simp; linarith))
    · by_contra hne
      exact htZ (Or.inl (Or.inr ⟨t - μ, ⟨⟨hpos, by linarith [htT.2, h.hμ]⟩,
        lt_of_le_of_ne (leftLim_le_self h.hU.1 _) hne⟩, by ring⟩))
  have := Gpath_left G h t
  rw [hlN, hlUμ] at this
  exact this

/-- Credit integrand. -/
noncomputable def G1 (b θ : ℝ) (a v : ℕ) : ℝ := if a < v then max (b - θ * ((v - a : ℕ) : ℝ)) 0 else 0

/-- Service indicator. -/
noncomputable def G2 (a v : ℕ) : ℝ := if a < v then 1 else 0

lemma vS_sum (n : ℕ) : (vS μ N U n : ℝ) = ∑ k ∈ Finset.Icc 1 n,
    G2 (vS μ N U (k - 1)) (vAv μ N U k) := by
  induction n with
  | zero => simp [vS, srec]
  | succ n ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ← ih, Nat.add_sub_cancel]
    unfold vS G2; simp only [srec]
    split_ifs <;> push_cast <;> ring

lemma orderCount_bound (h : PathOK μ N U) (T : ℝ) (hT : 0 ≤ T) :
    (epochSet (fun s => U (s - μ)) T).ncard + (if 0 < U (-μ) then 1 else 0) ≤ orderCount U T := by
  set V : ℝ → ℕ := fun s => U (s - μ) with hV
  set O := {t | t ∈ Icc 0 T ∧ leftLim U t < U t} with hO
  have hOfin : O.Finite := by
    apply ((epochSet_finite h.hU.1 T).union (finite_singleton (0:ℝ))).subset
    intro t ht
    rcases eq_or_lt_of_le ht.1.1 with h0 | hpos
    · exact Or.inr h0.symm
    · exact Or.inl ⟨⟨hpos, ht.1.2⟩, ht.2⟩
  have hEVfin := epochSet_finite (regPath_shift h.hU μ).1 T
  set W := ((fun e => e - μ) '' epochSet V T) ∪ (if 0 < U (-μ) then {(0:ℝ)} else ∅) with hW
  have hsub : W ⊆ O := by
    intro t ht
    rcases ht with ⟨e, he, rfl⟩ | ht
    · have hlt : leftLim U (e - μ) < U (e - μ) := by
        have := he.2; simp only [hV] at this; rwa [leftLim_shift] at this
      have hnn : 0 ≤ e - μ := by
        by_contra hc; push Not at hc
        rw [h.hU0 _ hc] at hlt; omega
      exact ⟨⟨hnn, by linarith [he.1.2, h.hμ]⟩, hlt⟩
    · split_ifs at ht with hpos
      · rw [mem_singleton_iff] at ht; subst ht
        have hμ0 : μ = 0 := by
          by_contra hc
          have : -μ < 0 := by have := h.hμ; push Not at hc; exact neg_neg_of_pos (lt_of_le_of_ne this (Ne.symm hc))
          rw [h.hU0 _ this] at hpos; omega
        rw [hμ0, neg_zero] at hpos
        refine ⟨⟨le_rfl, hT⟩, ?_⟩
        rw [leftLim_nonpos h.hU.1 h.hU0 le_rfl]; exact hpos
      · exact absurd ht (notMem_empty t)
  have hdisj : Disjoint ((fun e => e - μ) '' epochSet V T) (if 0 < U (-μ) then {(0:ℝ)} else ∅) := by
    split_ifs with hpos
    · rw [disjoint_singleton_right]
      rintro ⟨e, he, hz⟩
      have hμ0 : μ = 0 := by
        by_contra hc
        have : -μ < 0 := by have := h.hμ; push Not at hc; exact neg_neg_of_pos (lt_of_le_of_ne this (Ne.symm hc))
        rw [h.hU0 _ this] at hpos; omega
      simp only at hz; rw [hμ0] at hz; linarith [he.1.1]
    · exact disjoint_empty _
  have hcard : W.ncard = (epochSet V T).ncard + (if 0 < U (-μ) then 1 else 0) := by
    rw [hW, ncard_union_eq hdisj (hEVfin.image _) (by split_ifs <;> simp),
      ncard_image_of_injective _ (fun a b hab => by simpa using hab)]
    split_ifs <;> simp
  unfold orderCount
  rw [← hcard]
  exact ncard_le_ncard hsub hOfin

/-- Pathwise credit bound: credits at served demands are paid by orders. -/
theorem sc_pathwise (b θ : ℝ) (hθ : 0 < θ) (h : PathOK μ N U) {T : ℝ} (hT : 0 < T)
    (hgood : ∀ τ, 0 < τ → τ ≤ T → N τ ≤ leftLim N τ + 1) :
    ∑ k ∈ Finset.Icc 1 (N T), G1 b θ (vS μ N U (leftLim N (arrT N k))) (vAv μ N U k) ≤
      b ^ 2 / (2 * θ) * orderCount U T := by
  set kc := b ^ 2 / (2 * θ) with hkc
  have hkc0 : 0 ≤ kc := by positivity
  set V : ℝ → ℕ := fun s => U (s - μ) with hV
  have hVr : RegPath V := regPath_shift h.hU μ
  set EN := (epochSet_finite h.hN.1 T).toFinset with hEN
  set EV := (epochSet_finite hVr.1 T).toFinset with hEV
  set E := EN ∪ EV with hE
  have hEmem : ∀ e ∈ E, (0 < e ∧ e ≤ T) := by
    intro e he
    rcases Finset.mem_union.mp he with h1 | h1
    · exact (Set.Finite.mem_toFinset _).mp h1 |>.1
    · exact (Set.Finite.mem_toFinset _).mp h1 |>.1
  have hpw := piecewise_ftc (X := ℕ × ℕ) (fun ξ _ => Fp b θ (ξ.2 - ξ.1)) (fun _ _ => 0)
    (fun ξ a b hab => by simp)
    (fun ξ a b => intervalIntegrable_const)
    (fun t => (vA μ N U t, V t)) (fun e => (vS μ N U (leftLim N e), leftLim V e)) E T hT.le hEmem
    (by
      intro s t hs hst htT hno
      have hN' : N t = N s := const_of_noEpoch h.hN hs hst (fun τ h1 h2 h3 =>
        hno τ (Finset.mem_union_left _ ((Set.Finite.mem_toFinset _).mpr
          ⟨⟨by linarith, le_trans h2 htT⟩, h3⟩)) ⟨h1, h2⟩)
      have hV' : V t = V s := const_of_noEpoch hVr hs hst (fun τ h1 h2 h3 =>
        hno τ (Finset.mem_union_right _ ((Set.Finite.mem_toFinset _).mpr
          ⟨⟨by linarith, le_trans h2 htT⟩, h3⟩)) ⟨h1, h2⟩)
      simp only [vA, hN', hV'])
    (by
      intro e _
      obtain ⟨s1, hs1, he1⟩ := leftLim_attained h.hN.1 e
      obtain ⟨s2, hs2, he2⟩ := leftLim_attained hVr.1 e
      refine ⟨e - max s1 s2, by linarith [max_lt hs1 hs2], fun s hs1' hs2' => ?_⟩
      have h1 : s1 ≤ s := by linarith [le_max_left s1 s2]
      have h2 : s2 ≤ s := by linarith [le_max_right s1 s2]
      simp only [vA, he1 s h1 hs2', he2 s h2 hs2'])
  obtain ⟨-, hpot⟩ := hpw
  simp only [intervalIntegral.integral_zero, zero_add] at hpot
  -- order jumps
  set D : ℝ → ℝ := fun e => Fp b θ (leftLim V e - vA μ N U e) -
    Fp b θ (leftLim V e - vS μ N U (leftLim N e)) with hD
  have hjump : ∀ e ∈ E, D e - kc * (if e ∈ EV then 1 else 0) ≤
      Fp b θ (V e - vA μ N U e) - Fp b θ (leftLim V e - vS μ N U (leftLim N e)) := by
    intro e he
    have hmem := hEmem e he
    by_cases heV : e ∈ EV
    · rw [if_pos heV]; simp only [hD]
      have := Fp_ge b θ hθ (V e - vA μ N U e)
      have := Fp_nonpos b θ (leftLim V e - vA μ N U e)
      linarith
    · rw [if_neg heV]; simp only [hD]
      have : leftLim V e = V e := by
        by_contra hne
        exact heV ((Set.Finite.mem_toFinset _).mpr ⟨⟨hmem.1, hmem.2⟩,
          lt_of_le_of_ne (leftLim_le_self hVr.1 e) hne⟩)
      rw [this]; linarith
  have hD0 : ∀ e ∈ E, e ∉ EN → D e = 0 := by
    intro e he heN
    have hmem := hEmem e he
    have : leftLim N e = N e := by
      by_contra hne
      exact heN ((Set.Finite.mem_toFinset _).mpr ⟨⟨hmem.1, hmem.2⟩,
        lt_of_le_of_ne (leftLim_le_self h.hN.1 e) hne⟩)
    simp only [hD, vA, this, sub_self]
  have hNsum : ∑ e ∈ EN, D e = ∑ k ∈ Finset.Icc 1 (N T),
      G1 b θ (vS μ N U (leftLim N (arrT N k))) (vAv μ N U k) := by
    have hl_arr : ∀ k ∈ Finset.Icc 1 (N T), leftLim N (arrT N k) < k ∧ k ≤ N (arrT N k) ∧
        0 < arrT N k ∧ arrT N k ≤ T := by
      intro k hk
      have hk' := Finset.mem_Icc.mp hk
      have h1 := (arrT_spec h.hN h.hN0 hk'.1 hk'.2 (arrT N k)).mpr le_rfl
      refine ⟨?_, h1, arrT_pos h.hN h.hN0 hk'.1 hk'.2, arrT_le h.hN h.hN0 hk'.1 hk'.2⟩
      obtain ⟨s0, hs0, he0⟩ := leftLim_attained h.hN.1 (arrT N k)
      rw [← he0 s0 le_rfl hs0]
      by_contra hc; push Not at hc
      have := (arrT_spec h.hN h.hN0 hk'.1 hk'.2 s0).mp hc
      linarith
    apply Finset.sum_nbij' (fun e => N e) (fun k => arrT N k)
    · intro e he
      have he' := (Set.Finite.mem_toFinset _).mp he
      rw [Finset.mem_Icc]
      exact ⟨by have := he'.2; omega, h.hN.1 he'.1.2⟩
    · intro k hk
      obtain ⟨h2, h1, hσ0, hσT⟩ := hl_arr k hk
      exact (Set.Finite.mem_toFinset _).mpr ⟨⟨hσ0, hσT⟩, by omega⟩
    · intro e he
      have he' := (Set.Finite.mem_toFinset _).mp he
      exact arrT_eq_epoch h.hN h.hN0 he'.2 le_rfl
    · intro k hk
      obtain ⟨h2, h1, hσ0, hσT⟩ := hl_arr k hk
      have := hgood _ hσ0 hσT
      omega
    · intro e he
      have he' := (Set.Finite.mem_toFinset _).mp he
      have hk := he'.2
      have hgd := hgood e he'.1.1 he'.1.2
      have hl : leftLim N e = N e - 1 := by omega
      have hσ : arrT N (N e) = e := arrT_eq_epoch h.hN h.hN0 hk le_rfl
      have hav : vAv μ N U (N e) = leftLim V e := by
        unfold vAv; rw [hσ, hV, leftLim_shift]
      simp only [hD, hσ, vA, hl, hav]
      have hsucc : vS μ N U (N e) = vS μ N U (N e - 1) +
          if vS μ N U (N e - 1) < leftLim V e then 1 else 0 := by
        unfold vS
        conv_lhs => rw [show N e = (N e - 1) + 1 by omega]
        simp only [srec]
        rw [show N e - 1 + 1 = N e by omega, ← hav]
      rw [hsucc]
      unfold G1
      split_ifs with hlt
      · rw [show leftLim V e - vS μ N U (N e - 1) =
          (leftLim V e - (vS μ N U (N e - 1) + 1)) + 1 by omega, Fp_succ]
        push_cast; ring
      · simp
  have hEsum : ∑ e ∈ E, D e = ∑ e ∈ EN, D e := by
    symm
    exact Finset.sum_subset Finset.subset_union_left (fun e he heN => hD0 e he heN)
  have hEVs : ∑ e ∈ E, kc * (if e ∈ EV then (1:ℝ) else 0) = kc * EV.card := by
    rw [← Finset.mul_sum, Finset.sum_ite_mem, Finset.inter_eq_right.mpr Finset.subset_union_right]
    simp
  have hsumle := Finset.sum_le_sum hjump
  rw [Finset.sum_sub_distrib, hEsum, hNsum, hEVs] at hsumle
  -- endpoints
  have hT0 := Fp_nonpos b θ (V T - vA μ N U T)
  have hX0 : V 0 - vA μ N U 0 = U (-μ) := by
    simp only [hV, vA, h.hN0 0 le_rfl, zero_sub]; simp [vS, srec]
  have hF0 : -(kc * (if 0 < U (-μ) then 1 else 0)) ≤ Fp b θ (V 0 - vA μ N U 0) := by
    rw [hX0]
    split_ifs with hp
    · have := Fp_ge b θ hθ (U (-μ)); linarith
    · have : U (-μ) = 0 := by omega
      rw [this]; simp [Fp]
  have hcount := orderCount_bound h T hT.le
  have hEVcard : (EV.card : ℝ) = (epochSet V T).ncard := by
    rw [hEV, Set.ncard_eq_toFinset_card _ (epochSet_finite hVr.1 T)]
  have hcount' : (EV.card : ℝ) + (if 0 < U (-μ) then 1 else 0) ≤ orderCount U T := by
    rw [hEVcard]; exact_mod_cast hcount
  have : kc * ((EV.card : ℝ) + (if 0 < U (-μ) then 1 else 0)) ≤ kc * orderCount U T :=
    mul_le_mul_of_nonneg_left hcount' hkc0
  linarith

end scpath

end LostSalesRQ

namespace LostSalesRQ

open MeasureTheory ProbabilityTheory Filter Set Topology

lemma leftLim_zero_fun (t : ℝ) : leftLim (fun _ : ℝ => (0 : ℕ)) t = 0 :=
  le_antisymm (leftLim_le_self monotone_const t) (Nat.zero_le _)

lemma G1_nonneg (b θ : ℝ) (a v : ℕ) : 0 ≤ G1 b θ a v := by
  unfold G1; split_ifs
  · exact le_max_right _ _
  · exact le_rfl

lemma G2_nonneg (a v : ℕ) : 0 ≤ G2 a v := by unfold G2; split_ifs <;> norm_num

section scprob
variable (S : DemandSpace 1) (π : Policy S)

lemma served_emptyStart (hπ : π.EmptyStart) (μ t : ℝ) (ω : S.Ω) :
    π.served μ t ω = vA μ (fun s => S.N s ω) (fun s => π.U s ω) t := by
  have hinit : (fun s => π.init s ω) = fun _ => 0 := funext (fun s => hπ ω s)
  unfold Policy.served
  rw [hinit, servedPath_srec μ _ _ _ (S.regPath ω) (fun s hs => S.N_nonpos ω s hs)]
  unfold vA vS
  congr 1
  funext k
  unfold custAvail vAv
  rw [leftLim_zero_fun, zero_add]

lemma onHand_emptyStart (hπ : π.EmptyStart) (μ t : ℝ) (ω : S.Ω) :
    π.onHand μ t ω = π.U (t - μ) ω - vA μ (fun s => S.N s ω) (fun s => π.U s ω) t := by
  unfold Policy.onHand delivered
  rw [served_emptyStart S π hπ]
  simp only [hπ ω t, zero_add]

lemma measurable_Gproc (G : ℕ → ℕ → ℝ) (μ : ℝ) (hμ : 0 ≤ μ) (t : ℝ) :
    Measurable[S.𝓕 t] (fun ω => Gpath G μ (fun s => S.N s ω) (fun s => π.U s ω) t) := by
  unfold Gpath
  have hK : Measurable[S.𝓕 t] (fun ω => (vA μ (fun s => S.N s ω) (fun s => π.U s ω) t,
      π.U (t - μ) ω)) :=
    (measurable_vA S π μ hμ t).prodMk
      ((π.U_adapted (t - μ)).mono (S.𝓕.mono (by linarith)) le_rfl)
  exact (measurable_of_countable (fun p : ℕ × ℕ => G p.1 p.2)).comp hK

lemma measurable_Gpath_time (G : ℕ → ℕ → ℝ) {μ : ℝ} {N U : ℝ → ℕ} (h : PathOK μ N U) :
    Measurable (Gpath G μ N U) := by
  unfold Gpath
  have hvAm : Measurable (vA μ N U) := (measurable_from_nat (f := vS μ N U)).comp h.hN.1.measurable
  have hUmu : Measurable (fun t => U (t - μ)) := h.hU.1.measurable.comp (measurable_id.sub_const μ)
  exact (measurable_of_countable (fun p : ℕ × ℕ => G p.1 p.2)).comp (hvAm.prodMk hUmu)

theorem service_credit' (μ k θ T : ℝ) (hμ : 0 ≤ μ) (hk : 0 ≤ k) (hθ0 : 0 ≤ θ)
    (hT : 0 ≤ T) (hπ : π.EmptyStart) :
    ENNReal.ofReal (Real.sqrt (2 * k * θ)) * π.expectedServed μ T ≤
      ENNReal.ofReal θ * π.expectedHolding μ T + ENNReal.ofReal k * π.expectedOrders T := by
  set b := Real.sqrt (2 * k * θ) with hb
  -- degenerate cases
  by_cases hb0 : b = 0
  · rw [hb0, ENNReal.ofReal_zero, zero_mul]; exact zero_le
  have hθ : 0 < θ := by
    rcases eq_or_lt_of_le hθ0 with h | h
    · exfalso; apply hb0; rw [hb, ← h]; simp
    · exact h
  have hbpos : 0 < b := lt_of_le_of_ne (Real.sqrt_nonneg _) (Ne.symm hb0)
  have hb2 : b ^ 2 = 2 * k * θ := Real.sq_sqrt (by positivity)
  have hkc : b ^ 2 / (2 * θ) = k := by rw [hb2]; field_simp
  rcases eq_or_lt_of_le hT with hT0 | hTpos
  · subst hT0
    have : π.expectedServed μ 0 = 0 := by
      unfold Policy.expectedServed
      have : ∀ ω, (π.served μ 0 ω : ENNReal) = 0 := fun ω => by
        rw [served_emptyStart S π hπ]; unfold vA; simp [S.N_nonpos ω 0 le_rfl, vS, srec]
      simp [this]
    rw [this, mul_zero]; exact zero_le
  set T' := T with hT'
  -- the two integrands
  set H1 : ℝ → S.Ω → ℝ := fun t ω => Gpath (G1 b θ) μ (fun s => S.N s ω) (fun s => π.U s ω) t
  set H2 : ℝ → S.Ω → ℝ := fun t ω => Gpath G2 μ (fun s => S.N s ω) (fun s => π.U s ω) t
  set Hl1 : ℕ → S.Ω → ℝ := fun k ω => G1 b θ
    (vS μ (fun s => S.N s ω) (fun s => π.U s ω) (leftLim (fun s => S.N s ω) (arrT (fun s => S.N s ω) k)))
    (vAv μ (fun s => S.N s ω) (fun s => π.U s ω) k)
  set Hl2 : ℕ → S.Ω → ℝ := fun k ω => G2
    (vS μ (fun s => S.N s ω) (fun s => π.U s ω) (leftLim (fun s => S.N s ω) (arrT (fun s => S.N s ω) k)))
    (vAv μ (fun s => S.N s ω) (fun s => π.U s ω) k)
  have hG1b : ∀ a v, |G1 b θ a v| ≤ b := by
    intro a v; unfold G1; split_ifs
    · rw [abs_of_nonneg (le_max_right _ _)]
      exact max_le (by have := Nat.cast_nonneg (α := ℝ) (v - a); nlinarith) hbpos.le
    · simp; exact hbpos.le
  have hG2b : ∀ a v, |G2 a v| ≤ 1 := by intro a v; unfold G2; split_ifs <;> simp
  have hc1 := compensation S T hTpos H1 b
    (fun t _ => measurable_Gproc S π (G1 b θ) μ hμ t) (fun t ω => hG1b _ _) Hl1
    (fun ω k _ _ => Gpath_left (G1 b θ) (π.pathOK S μ hμ ω) _)
    (fun ω => Gpath_left_ae (G1 b θ) (π.pathOK S μ hμ ω) T)
  have hc2 := compensation S T hTpos H2 1
    (fun t _ => measurable_Gproc S π G2 μ hμ t) (fun t ω => hG2b _ _) Hl2
    (fun ω k _ _ => Gpath_left G2 (π.pathOK S μ hμ ω) _)
    (fun ω => Gpath_left_ae G2 (π.pathOK S μ hμ ω) T)
  obtain ⟨hi1a, hi1b, he1⟩ := hc1
  obtain ⟨hi2a, hi2b, he2⟩ := hc2
  -- pathwise facts on good paths
  have hgood := ae_noBatch S T hTpos
  have hsum2 : ∀ᵐ ω ∂S.ν, ((π.served μ T ω : ℕ) : ℝ) = ∑ k ∈ Finset.Icc 1 (S.N T ω), Hl2 k ω := by
    filter_upwards [hgood] with ω hω
    have h := π.pathOK S μ hμ ω
    rw [served_emptyStart S π hπ]
    unfold vA
    rw [vS_sum]
    apply Finset.sum_congr rfl
    intro k hk
    have hk' := Finset.mem_Icc.mp hk
    have hσ0 := arrT_pos h.hN h.hN0 hk'.1 hk'.2
    have hσT := arrT_le h.hN h.hN0 hk'.1 hk'.2
    have h1 := (arrT_spec h.hN h.hN0 hk'.1 hk'.2 (arrT _ k)).mpr le_rfl
    have h2 : leftLim (fun s => S.N s ω) (arrT (fun s => S.N s ω) k) < k := by
      obtain ⟨s0, hs0, he0⟩ := leftLim_attained h.hN.1 (arrT (fun s => S.N s ω) k)
      rw [← he0 s0 le_rfl hs0]
      by_contra hc; push Not at hc
      have := (arrT_spec h.hN h.hN0 hk'.1 hk'.2 s0).mp hc
      linarith
    have := hω _ hσ0 hσT
    have hl : leftLim (fun s => S.N s ω) (arrT (fun s => S.N s ω) k) = k - 1 := by
      first | omega | (beta_reduce at this h1; omega)
    simp only [Hl2]; rw [hl]
  have hsum1 : ∀ᵐ ω ∂S.ν, ∑ k ∈ Finset.Icc 1 (S.N T ω), Hl1 k ω ≤ k * (π.orders T ω : ℝ) := by
    filter_upwards [hgood] with ω hω
    have := sc_pathwise b θ hθ (π.pathOK S μ hμ ω) hTpos hω
    rw [hkc] at this
    exact this
  -- pointwise in time
  have hX : ∀ ω, IntervalIntegrable
      (fun t => ((π.U (t - μ) ω - vA μ (fun s => S.N s ω) (fun s => π.U s ω) t : ℕ) : ℝ)) volume 0 T := by
    intro ω
    have h := π.pathOK S μ hμ ω
    have hm := measurable_Gpath_time (fun a v => ((v - a : ℕ) : ℝ)) h
    rw [intervalIntegrable_iff]
    refine Measure.integrableOn_of_bounded (M := (π.U T ω : ℝ)) (by simp) hm.aestronglyMeasurable ?_
    rw [uIoc_of_le hT]
    refine ae_restrict_of_forall_mem measurableSet_Ioc (fun t ht => ?_)
    rw [Real.norm_eq_abs, Nat.abs_cast]
    have : π.U (t - μ) ω - vA μ (fun s => S.N s ω) (fun s => π.U s ω) t ≤ π.U T ω :=
      le_trans (Nat.sub_le _ _) (π.U_mono ω (by linarith [ht.2]))
    exact_mod_cast this
  have hpt : ∀ ω, b * ∫ t in (0:ℝ)..T, H2 t ω ≤ (∫ t in (0:ℝ)..T, H1 t ω) +
      θ * ∫ t in (0:ℝ)..T,
        ((π.U (t - μ) ω - vA μ (fun s => S.N s ω) (fun s => π.U s ω) t : ℕ) : ℝ) := by
    intro ω
    have h := π.pathOK S μ hμ ω
    have hi1 : IntervalIntegrable (fun t => H1 t ω) volume 0 T :=
      intervalIntegrable_of_bdd (measurable_Gpath_time _ h) (fun t => hG1b _ _) 0 T
    have hi2 : IntervalIntegrable (fun t => H2 t ω) volume 0 T :=
      intervalIntegrable_of_bdd (measurable_Gpath_time _ h) (fun t => hG2b _ _) 0 T
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul,
      ← intervalIntegral.integral_add hi1 ((hX ω).const_mul θ)]
    apply intervalIntegral.integral_mono_on hT (hi2.const_mul b) (hi1.add ((hX ω).const_mul θ))
    intro t _
    simp only [H1, H2, Gpath, G1, G2]
    split_ifs with hlt
    · have := le_max_left (b - θ * ((π.U (t - μ) ω - vA μ (fun s => S.N s ω)
        (fun s => π.U s ω) t : ℕ) : ℝ)) 0
      linarith
    · have := Nat.cast_nonneg (α := ℝ) (π.U (t - μ) ω - vA μ (fun s => S.N s ω)
        (fun s => π.U s ω) t)
      nlinarith
  -- nonnegativity
  have hH1nn : ∀ ω, 0 ≤ ∫ t in (0:ℝ)..T, H1 t ω := fun ω =>
    intervalIntegral.integral_nonneg hT (fun t _ => by
      simp only [H1, Gpath, G1]; split_ifs
      · exact le_max_right _ _
      · exact le_rfl)
  have hH2nn : ∀ ω, 0 ≤ ∫ t in (0:ℝ)..T, H2 t ω := fun ω =>
    intervalIntegral.integral_nonneg hT (fun t _ => by
      simp only [H2, Gpath, G2]; split_ifs <;> norm_num)
  have hS1nn : ∀ ω, 0 ≤ ∑ k ∈ Finset.Icc 1 (S.N T ω), Hl1 k ω := fun ω =>
    Finset.sum_nonneg (fun k _ => G1_nonneg _ _ _ _)
  have hS2nn : ∀ ω, 0 ≤ ∑ k ∈ Finset.Icc 1 (S.N T ω), Hl2 k ω := fun ω =>
    Finset.sum_nonneg (fun k _ => G2_nonneg _ _)
  -- assemble
  have hserved : π.expectedServed μ T =
      ENNReal.ofReal (∫ ω, (∫ t in (0:ℝ)..T, H2 t ω) ∂S.ν) := by
    unfold Policy.expectedServed
    rw [← he2, ofReal_integral_eq_lintegral_ofReal hi2a (Eventually.of_forall hS2nn)]
    apply lintegral_congr_ae
    filter_upwards [hsum2] with ω hω
    rw [← hω, ENNReal.ofReal_natCast]
  have hholding : π.expectedHolding μ T = ∫⁻ ω, ENNReal.ofReal (∫ t in (0:ℝ)..T,
      ((π.U (t - μ) ω - vA μ (fun s => S.N s ω) (fun s => π.U s ω) t : ℕ) : ℝ)) ∂S.ν := by
    unfold Policy.expectedHolding
    apply lintegral_congr
    intro ω
    have h := π.pathOK S μ hμ ω
    have hm : Measurable (fun t => π.U (t - μ) ω - vA μ (fun s => S.N s ω) (fun s => π.U s ω) t) :=
      (h.hU.1.measurable.comp (measurable_id.sub_const μ)).sub
        ((measurable_from_nat (f := vS μ _ _)).comp h.hN.1.measurable)
    rw [← lintegral_Icc_natCast hm hT (C := π.U T ω) (fun t ht => by
      have : π.U (t - μ) ω - vA μ (fun s => S.N s ω) (fun s => π.U s ω) t ≤ π.U T ω :=
        le_trans (Nat.sub_le _ _) (π.U_mono ω (by linarith [ht.2]))
      exact_mod_cast this)]
    apply setLIntegral_congr_fun measurableSet_Icc
    intro t _
    simp only [onHand_emptyStart S π hπ]
  have hH1 : ∫⁻ ω, ENNReal.ofReal (∫ t in (0:ℝ)..T, H1 t ω) ∂S.ν ≤
      ENNReal.ofReal k * π.expectedOrders T := by
    rw [← ofReal_integral_eq_lintegral_ofReal hi1b (Eventually.of_forall hH1nn), ← he1]
    calc ENNReal.ofReal (∫ ω, ∑ k ∈ Finset.Icc 1 (S.N T ω), Hl1 k ω ∂S.ν)
        ≤ ∫⁻ ω, ENNReal.ofReal (∑ k ∈ Finset.Icc 1 (S.N T ω), Hl1 k ω) ∂S.ν :=
          ofReal_integral_le hi1a
      _ ≤ ∫⁻ ω, ENNReal.ofReal k * (π.orders T ω : ENNReal) ∂S.ν := by
          apply lintegral_mono_ae
          filter_upwards [hsum1] with ω hω
          rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul hk]
          exact ENNReal.ofReal_le_ofReal hω
      _ = ENNReal.ofReal k * π.expectedOrders T := by
          unfold Policy.expectedOrders
          rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  rw [hserved, hholding, ← ENNReal.ofReal_mul hbpos.le, ← integral_const_mul]
  calc ENNReal.ofReal (∫ ω, b * (∫ t in (0:ℝ)..T, H2 t ω) ∂S.ν)
      ≤ ∫⁻ ω, ENNReal.ofReal (b * ∫ t in (0:ℝ)..T, H2 t ω) ∂S.ν :=
        ofReal_integral_le (hi2b.const_mul b)
    _ ≤ ∫⁻ ω, (ENNReal.ofReal (∫ t in (0:ℝ)..T, H1 t ω) + ENNReal.ofReal θ *
          ENNReal.ofReal (∫ t in (0:ℝ)..T,
            ((π.U (t - μ) ω - vA μ (fun s => S.N s ω) (fun s => π.U s ω) t : ℕ) : ℝ))) ∂S.ν := by
        apply lintegral_mono
        intro ω
        simp only []
        rw [← ENNReal.ofReal_mul hθ0]
        exact le_trans (ENNReal.ofReal_le_ofReal (hpt ω)) ENNReal.ofReal_add_le
    _ = (∫⁻ ω, ENNReal.ofReal (∫ t in (0:ℝ)..T, H1 t ω) ∂S.ν) + ENNReal.ofReal θ *
          ∫⁻ ω, ENNReal.ofReal (∫ t in (0:ℝ)..T,
            ((π.U (t - μ) ω - vA μ (fun s => S.N s ω) (fun s => π.U s ω) t : ℕ) : ℝ)) ∂S.ν := by
        rw [lintegral_add_left' hi1b.aemeasurable.ennreal_ofReal,
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ ≤ _ := by rw [add_comm]; gcongr

end scprob

end LostSalesRQ


namespace LostSalesRQ

open MeasureTheory ProbabilityTheory Filter Set Topology

section otcopy
variable (S : DemandSpace 1) (π : Policy S)

/-- The physically empty copy of π: same orders, no initial supply. -/
def emptyCopy : Policy S where
  init := fun _ _ => 0
  U := π.U
  init_meas := fun _ => measurable_const
  init_nonpos := fun _ _ _ => rfl
  init_mono := fun _ => monotone_const
  init_rcont := fun _ _ => ⟨1, one_pos, fun _ _ _ => rfl⟩
  init_bdd := fun _ => ⟨0, fun _ => le_rfl⟩
  U_adapted := π.U_adapted
  U_nonpos := π.U_nonpos
  U_mono := π.U_mono
  U_rcont := π.U_rcont

lemma emptyCopy_empty : (emptyCopy S π).EmptyStart := fun _ _ => rfl

lemma copy_served (μ t : ℝ) (ω : S.Ω) :
    (emptyCopy S π).served μ t ω = vA μ (fun s => S.N s ω) (fun s => π.U s ω) t :=
  served_emptyStart S (emptyCopy S π) (emptyCopy_empty S π) μ t ω

lemma copy_onHand (μ t : ℝ) (ω : S.Ω) :
    (emptyCopy S π).onHand μ t ω = π.U (t - μ) ω - vA μ (fun s => S.N s ω) (fun s => π.U s ω) t :=
  onHand_emptyStart S (emptyCopy S π) (emptyCopy_empty S π) μ t ω

lemma copy_cmp (μ T : ℝ) (hμ : 0 ≤ μ) (hT : 0 ≤ T) (ω : S.Ω) :
    (∀ t ∈ Icc 0 T, (emptyCopy S π).onHand μ t ω ≤ π.onHand μ t ω) ∧
    (emptyCopy S π).lost μ T ω ≤ π.lost μ T ω + min (π.init T ω) (S.N T ω) := by
  have h := π.pathOK S μ hμ ω
  set N : ℝ → ℕ := fun s => S.N s ω with hN
  set U : ℝ → ℕ := fun s => π.U s ω with hU
  set I0 : ℝ → ℕ := fun s => π.init s ω with hI0
  have hI0m : Monotone I0 := π.init_mono ω
  set ic : ℕ → ℕ := fun k => leftLim I0 (arrT N k) with hic
  have hcust : ∀ k, custAvail μ I0 U N k = vAv μ N U k + ic k := fun k => by
    unfold custAvail vAv; rw [hic]; ring
  have hcmp := srec_cmp (custAvail μ I0 U N) (vAv μ N U) ic (N T)
    (fun k _ _ => hcust k)
    (fun k k' hk hkk hk' => leftLim_mono hI0m
      (arrT_mono' h.hN (fun s hs => h.hN0 s hs.le) hk hkk hk'))
  have hserved : ∀ t, π.served μ t ω = srec (custAvail μ I0 U N) (N t) := fun t =>
    servedPath_srec μ I0 U N h.hN h.hN0 t
  have hic_le : ∀ t, 0 ≤ t → N t ≤ N T → (if N t = 0 then 0 else ic (N t)) ≤ I0 t := by
    intro t ht _
    split_ifs with h0
    · exact Nat.zero_le _
    · have hpos : 1 ≤ N t := Nat.one_le_iff_ne_zero.mpr h0
      have hσ := arrT_le h.hN h.hN0 hpos (le_refl (N t))
      exact le_trans (leftLim_le_self hI0m _) (hI0m hσ)
  refine ⟨fun t ht => ?_, ?_⟩
  · have hNt : N t ≤ N T := h.hN.1 ht.2
    obtain ⟨_, h2⟩ := hcmp (N t) hNt
    have h3 := hic_le t ht.1 hNt
    rw [copy_onHand]
    unfold Policy.onHand delivered
    rw [hserved t]
    unfold vA vS
    simp only [hN, hU, hI0] at h2 h3 ⊢
    omega
  · obtain ⟨h1, h2⟩ := hcmp (N T) le_rfl
    have h3 := hic_le T hT le_rfl
    have h4 := srec_le (custAvail μ I0 U N) (N T)
    unfold Policy.lost
    rw [hserved T, copy_served]
    unfold vA vS
    simp only [hN, hU, hI0] at h1 h2 h3 h4 ⊢
    omega

lemma copy_served_add_lost (μ T : ℝ) (ω : S.Ω) :
    (emptyCopy S π).served μ T ω + (emptyCopy S π).lost μ T ω = S.N T ω := by
  unfold Policy.lost
  have : (emptyCopy S π).served μ T ω ≤ S.N T ω := by
    rw [copy_served]; unfold vA vS; exact srec_le _ _
  omega

lemma measurable_copy_lost (μ T : ℝ) (hμ : 0 ≤ μ) :
    Measurable (fun ω => ((emptyCopy S π).lost μ T ω : ENNReal)) := by
  have hA : Measurable (fun ω => vA μ (fun s => S.N s ω) (fun s => π.U s ω) T) :=
    (measurable_vA S π μ hμ T).mono (S.𝓕.le T) le_rfl
  have heq : ∀ ω, (emptyCopy S π).lost μ T ω =
      S.N T ω - vA μ (fun s => S.N s ω) (fun s => π.U s ω) T := by
    intro ω; unfold Policy.lost; rw [copy_served]
  simp_rw [heq]
  exact (measurable_of_countable (fun n : ℕ => (n : ENNReal))).comp ((S.measurable_N T).sub hA)

lemma lintegral_N (T : ℝ) (hT : 0 ≤ T) : ∫⁻ ω, (S.N T ω : ENNReal) ∂S.ν = ENNReal.ofReal T := by
  have h := S.lintegral_inc le_rfl hT (by linarith)
  have hinc : ∀ ω, S.inc 0 T ω = S.N T ω := fun ω => by
    unfold DemandSpace.inc; rw [S.N_nonpos ω 0 le_rfl, Nat.sub_zero]
  simp only [hinc, one_mul, sub_zero] at h
  exact h

end otcopy

end LostSalesRQ

namespace LostSalesRQ

open MeasureTheory ProbabilityTheory Filter Set Topology

section othor
variable (S : DemandSpace 1) (π : Policy S)

/-- Finite-horizon operating transform. -/
theorem ot_horizon (μ a k θ T : ℝ) (hμ : 0 ≤ μ) (ha : 0 ≤ a) (hk : 0 ≤ k) (hθ0 : 0 ≤ θ)
    (hθ1 : θ < 1) (hba : Real.sqrt (2 * k * θ) ≤ a) (hT : 0 ≤ T) :
    ENNReal.ofReal (Real.sqrt (2 * k * θ)) * ENNReal.ofReal T +
        ENNReal.ofReal (1 - θ) * ∫⁻ ω, (emptyCopy S π).horizonCost μ 1
          ((a - Real.sqrt (2 * k * θ)) / (1 - θ)) 0 T ω ∂S.ν ≤
      (∫⁻ ω, π.horizonCost μ 1 a k T ω ∂S.ν) +
        ENNReal.ofReal a * ∫⁻ ω, ((min (π.init T ω) (S.N T ω) : ℕ) : ENNReal) ∂S.ν := by
  set b := Real.sqrt (2 * k * θ) with hb
  set a' := (a - b) / (1 - θ) with ha'
  set π0 := emptyCopy S π with hπ0
  have hb0 : 0 ≤ b := Real.sqrt_nonneg _
  have h1θ : 0 < 1 - θ := by linarith
  have ha'0 : 0 ≤ a' := div_nonneg (by linarith) h1θ.le
  -- the pieces
  set H0 := ∫⁻ ω, (∫⁻ t in Icc 0 T, (π0.onHand μ t ω : ENNReal)) ∂S.ν with hH0
  set H := ∫⁻ ω, (∫⁻ t in Icc 0 T, (π.onHand μ t ω : ENNReal)) ∂S.ν with hH
  set L0 := ∫⁻ ω, (π0.lost μ T ω : ENNReal) ∂S.ν with hL0
  set L := ∫⁻ ω, (π.lost μ T ω : ENNReal) ∂S.ν with hL
  set O := ∫⁻ ω, (π.orders T ω : ENNReal) ∂S.ν with hO
  set A0 := ∫⁻ ω, (π0.served μ T ω : ENNReal) ∂S.ν with hA0
  set Mi := ∫⁻ ω, ((min (π.init T ω) (S.N T ω) : ℕ) : ENNReal) ∂S.ν with hMi
  have hmeasL0 := measurable_copy_lost S π μ T hμ
  have hmeasmin : Measurable (fun ω => ((min (π.init T ω) (S.N T ω) : ℕ) : ENNReal)) := by
    have h1 : Measurable (π.init T) := (π.init_meas T).mono (S.𝓕.le 0) le_rfl
    exact (measurable_of_countable (fun p : ℕ × ℕ => ((min p.1 p.2 : ℕ) : ENNReal))).comp
      (h1.prodMk (S.measurable_N T))
  -- copy cost
  have hcopy : ∫⁻ ω, π0.horizonCost μ 1 a' 0 T ω ∂S.ν = H0 + ENNReal.ofReal a' * L0 := by
    unfold Policy.horizonCost
    simp only [ENNReal.ofReal_one, one_mul, ENNReal.ofReal_zero, zero_mul, add_zero]
    rw [lintegral_add_right _ (hmeasL0.const_mul _), lintegral_const_mul _ hmeasL0]
  -- policy cost
  have hcost : H + ENNReal.ofReal a * L + ENNReal.ofReal k * O ≤
      ∫⁻ ω, π.horizonCost μ 1 a k T ω ∂S.ν := by
    unfold Policy.horizonCost
    simp only [ENNReal.ofReal_one, one_mul]
    calc H + ENNReal.ofReal a * L + ENNReal.ofReal k * O
        = (∫⁻ ω, (∫⁻ t in Icc 0 T, (π.onHand μ t ω : ENNReal)) ∂S.ν) +
          (∫⁻ ω, ENNReal.ofReal a * (π.lost μ T ω : ENNReal) ∂S.ν) +
          ∫⁻ ω, ENNReal.ofReal k * (π.orders T ω : ENNReal) ∂S.ν := by
          rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
            lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      _ ≤ (∫⁻ ω, ((∫⁻ t in Icc 0 T, (π.onHand μ t ω : ENNReal)) +
            ENNReal.ofReal a * (π.lost μ T ω : ENNReal)) ∂S.ν) +
          ∫⁻ ω, ENNReal.ofReal k * (π.orders T ω : ENNReal) ∂S.ν := by
          gcongr; exact le_lintegral_add _ _
      _ ≤ _ := le_lintegral_add _ _
  -- pathwise comparisons
  have hHH : H0 ≤ H := lintegral_mono (fun ω =>
    setLIntegral_mono' measurableSet_Icc (fun t ht => by
      exact_mod_cast (copy_cmp S π μ T hμ hT ω).1 t ht))
  have hLL : L0 ≤ L + Mi := by
    rw [hL, hMi, ← lintegral_add_right _ hmeasmin]
    refine lintegral_mono (fun ω => ?_)
    have h2 := (copy_cmp S π μ T hμ hT ω).2
    simp only [hπ0] at h2 ⊢
    exact_mod_cast h2
  have hAL : A0 + L0 = ENNReal.ofReal T := by
    rw [hA0, hL0, ← lintegral_add_right _ hmeasL0, ← lintegral_N S T hT]
    exact lintegral_congr (fun ω => by exact_mod_cast copy_served_add_lost S π μ T ω)
  -- service credit for the empty copy
  have hsc := service_credit' S π0 μ k θ T hμ hk hθ0 hT (emptyCopy_empty S π)
  have hsc' : ENNReal.ofReal b * A0 ≤ ENNReal.ofReal θ * H0 + ENNReal.ofReal k * O := hsc
  -- arithmetic
  have hsplitH : H0 = ENNReal.ofReal θ * H0 + ENNReal.ofReal (1 - θ) * H0 := by
    rw [← add_mul, ← ENNReal.ofReal_add hθ0 h1θ.le, add_sub_cancel, ENNReal.ofReal_one, one_mul]
  have hsplita : ENNReal.ofReal a = ENNReal.ofReal b + ENNReal.ofReal (1 - θ) * ENNReal.ofReal a' := by
    rw [← ENNReal.ofReal_mul h1θ.le, ← ENNReal.ofReal_add hb0 (by positivity)]
    congr 1; rw [ha']; field_simp; ring
  rw [hcopy]
  calc ENNReal.ofReal b * ENNReal.ofReal T + ENNReal.ofReal (1 - θ) * (H0 + ENNReal.ofReal a' * L0)
      = ENNReal.ofReal b * A0 + ENNReal.ofReal (1 - θ) * H0 +
          (ENNReal.ofReal b + ENNReal.ofReal (1 - θ) * ENNReal.ofReal a') * L0 := by
        rw [← hAL]; ring
    _ ≤ (ENNReal.ofReal θ * H0 + ENNReal.ofReal k * O) + ENNReal.ofReal (1 - θ) * H0 +
          ENNReal.ofReal a * (L + Mi) := by
        rw [← hsplita]; gcongr
    _ = (ENNReal.ofReal θ * H0 + ENNReal.ofReal (1 - θ) * H0) + ENNReal.ofReal a * L +
          ENNReal.ofReal k * O + ENNReal.ofReal a * Mi := by ring
    _ = H0 + ENNReal.ofReal a * L + ENNReal.ofReal k * O + ENNReal.ofReal a * Mi := by
        rw [← hsplitH]
    _ ≤ H + ENNReal.ofReal a * L + ENNReal.ofReal k * O + ENNReal.ofReal a * Mi := by gcongr
    _ ≤ _ := by gcongr

end othor

end LostSalesRQ

namespace LostSalesRQ

open MeasureTheory ProbabilityTheory Filter Set Topology

lemma limsup_add_null (x w : ℝ → ENNReal) (hw : limsup w atTop = 0) :
    limsup (fun T => x T + w T) atTop ≤ limsup x atTop := by
  refine ENNReal.le_of_forall_pos_le_add (fun ε hε _ => ?_)
  have hev : ∀ᶠ T in atTop, w T < ε :=
    eventually_lt_of_limsup_lt (by rw [hw]; exact_mod_cast hε)
  calc limsup (fun T => x T + w T) atTop ≤ limsup (fun T => x T + (ε : ENNReal)) atTop :=
        limsup_le_limsup (hev.mono fun T hT => add_le_add le_rfl hT.le) (by isBoundedDefault) (by isBoundedDefault)
    _ = limsup x atTop + ε := limsup_add_const atTop x _ (by isBoundedDefault) (by isBoundedDefault)

section otlim
variable (S : DemandSpace 1) (π : Policy S)

/-- Initial supply is negligible on average. -/
lemma init_negligible (a : ℝ) (ha : 0 ≤ a) :
    limsup (fun T : ℝ => ENNReal.ofReal a *
      (∫⁻ ω, ((min (π.init T ω) (S.N T ω) : ℕ) : ENNReal) ∂S.ν) / ENNReal.ofReal T) atTop = 0 := by
  set w : ℝ → ENNReal := fun T => ENNReal.ofReal a *
      (∫⁻ ω, ((min (π.init T ω) (S.N T ω) : ℕ) : ENNReal) ∂S.ν) / ENNReal.ofReal T with hw
  have hn : ∀ n : ℕ, limsup w atTop ≤ ENNReal.ofReal (a * (S.ν (bigInit S π n)).toReal) := by
    intro n
    set p := (S.ν (bigInit S π n)).toReal with hp
    have hlim : Tendsto (fun T : ℝ => ENNReal.ofReal (a * n / T + a * p)) atTop
        (𝓝 (ENNReal.ofReal (a * p))) := by
      apply ENNReal.tendsto_ofReal
      have : Tendsto (fun T : ℝ => a * n / T) atTop (𝓝 0) :=
        tendsto_const_nhds.div_atTop tendsto_id
      simpa using this.add_const (a * p)
    rw [← hlim.limsup_eq]
    apply limsup_le_limsup _ (by isBoundedDefault) (by isBoundedDefault)
    filter_upwards [eventually_gt_atTop 0] with T hT
    simp only [hw]
    rw [ENNReal.div_le_iff_le_mul (Or.inl (by simpa using hT)) (Or.inl ENNReal.ofReal_ne_top),
      ← ENNReal.ofReal_mul (by positivity)]
    calc ENNReal.ofReal a * ∫⁻ ω, ((min (π.init T ω) (S.N T ω) : ℕ) : ENNReal) ∂S.ν
        ≤ ENNReal.ofReal a * ENNReal.ofReal (n + T * p) := by
          gcongr; exact init_tail S π T hT n
      _ = ENNReal.ofReal ((a * n / T + a * p) * T) := by
          rw [← ENNReal.ofReal_mul ha]; congr 1; field_simp
  apply le_antisymm _ (zero_le)
  have ht : Tendsto (fun n : ℕ => ENNReal.ofReal (a * (S.ν (bigInit S π n)).toReal)) atTop (𝓝 0) := by
    have h1 := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp (tendsto_bigInit S π)
    have h2 := ENNReal.tendsto_ofReal (h1.const_mul a)
    simpa using h2
  exact ge_of_tendsto' ht hn

/-- Policy-level operating transform. -/
theorem ot_policy (μ a k θ : ℝ) (hμ : 0 ≤ μ) (ha : 0 ≤ a) (hk : 0 ≤ k) (hθ0 : 0 ≤ θ)
    (hθ1 : θ < 1) (hba : Real.sqrt (2 * k * θ) ≤ a) :
    ENNReal.ofReal (Real.sqrt (2 * k * θ)) + ENNReal.ofReal (1 - θ) *
        (emptyCopy S π).avgCost μ 1 ((a - Real.sqrt (2 * k * θ)) / (1 - θ)) 0 ≤
      π.avgCost μ 1 a k := by
  set b := Real.sqrt (2 * k * θ) with hb
  set a' := (a - b) / (1 - θ) with ha'
  set x : ℝ → ENNReal := fun T => (∫⁻ ω, π.horizonCost μ 1 a k T ω ∂S.ν) / ENNReal.ofReal T
  set y : ℝ → ENNReal := fun T =>
    (∫⁻ ω, (emptyCopy S π).horizonCost μ 1 a' 0 T ω ∂S.ν) / ENNReal.ofReal T
  set w : ℝ → ENNReal := fun T => ENNReal.ofReal a *
      (∫⁻ ω, ((min (π.init T ω) (S.N T ω) : ℕ) : ENNReal) ∂S.ν) / ENNReal.ofReal T
  have hev : ∀ᶠ T in atTop, ENNReal.ofReal b + ENNReal.ofReal (1 - θ) * y T ≤ x T + w T := by
    filter_upwards [eventually_gt_atTop 0] with T hT
    have hT0 : ENNReal.ofReal T ≠ 0 := by simpa using hT
    have key := ot_horizon S π μ a k θ T hμ ha hk hθ0 hθ1 hba hT.le
    have := ENNReal.div_le_div_right key (ENNReal.ofReal T)
    rw [ENNReal.add_div, ENNReal.add_div, ENNReal.mul_div_cancel_right hT0 ENNReal.ofReal_ne_top,
      mul_div_assoc] at this
    exact this
  have h1 : limsup (fun T => ENNReal.ofReal b + ENNReal.ofReal (1 - θ) * y T) atTop =
      ENNReal.ofReal b + ENNReal.ofReal (1 - θ) * limsup y atTop := by
    rw [limsup_const_add atTop _ _ (by isBoundedDefault) (by isBoundedDefault),
      ENNReal.limsup_const_mul_of_ne_top ENNReal.ofReal_ne_top]
  have h2 : limsup (fun T => ENNReal.ofReal b + ENNReal.ofReal (1 - θ) * y T) atTop ≤
      limsup x atTop :=
    le_trans (limsup_le_limsup hev (by isBoundedDefault) (by isBoundedDefault))
      (limsup_add_null x w (init_negligible S π a ha))
  rw [h1] at h2
  exact h2

end otlim

theorem operating_transform' (μ a k : ℝ) (hμ : 0 ≤ μ) (ha : 0 ≤ a) (hk : 0 ≤ k) :
    (∀ θ : ℝ, 0 ≤ θ → θ < 1 → Real.sqrt (2 * k * θ) ≤ a →
      ENNReal.ofReal (Real.sqrt (2 * k * θ)) +
          ENNReal.ofReal (1 - θ) * OPTk μ ((a - Real.sqrt (2 * k * θ)) / (1 - θ)) 0 ≤
        OPTk μ a k) ∧
    ENNReal.ofReal (min a (Real.sqrt (2 * k))) ≤ OPTk μ a k := by
  have part1 : ∀ θ : ℝ, 0 ≤ θ → θ < 1 → Real.sqrt (2 * k * θ) ≤ a →
      ENNReal.ofReal (Real.sqrt (2 * k * θ)) +
          ENNReal.ofReal (1 - θ) * OPTk μ ((a - Real.sqrt (2 * k * θ)) / (1 - θ)) 0 ≤
        OPTk μ a k := by
    intro θ hθ0 hθ1 hba
    conv_rhs => unfold OPTk OPT
    refine le_iInf₂ (fun S π => le_trans ?_ (ot_policy S π μ a k θ hμ ha hk hθ0 hθ1 hba))
    gcongr
    unfold OPTk OPT
    exact iInf₂_le S (emptyCopy S π)
  have lb : ∀ θ : ℝ, 0 ≤ θ → θ < 1 → Real.sqrt (2 * k * θ) ≤ a →
      ENNReal.ofReal (Real.sqrt (2 * k * θ)) ≤ OPTk μ a k :=
    fun θ h0 h1 h2 => le_trans le_self_add (part1 θ h0 h1 h2)
  refine ⟨part1, ?_⟩
  by_cases hk0 : k = 0
  · subst hk0; simp
  have hkpos : 0 < k := lt_of_le_of_ne hk (Ne.symm hk0)
  rcases le_or_gt (Real.sqrt (2 * k)) a with hsa | hsa
  · rw [min_eq_right hsa]
    have hlim : Tendsto (fun n : ℕ => ENNReal.ofReal (Real.sqrt (2 * k * (1 - 1 / ((n : ℝ) + 2)))))
        atTop (𝓝 (ENNReal.ofReal (Real.sqrt (2 * k)))) := by
      apply ENNReal.tendsto_ofReal
      have h1 : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 2)) atTop (𝓝 0) := by
        have := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
        refine squeeze_zero (fun n => by positivity) (fun n => ?_) this
        apply one_div_le_one_div_of_le (by positivity); linarith
      have h2 := ((tendsto_const_nhds (x := (1:ℝ))).sub h1).const_mul (2 * k)
      have h3 := (Real.continuous_sqrt.tendsto _).comp h2
      rw [sub_zero, mul_one] at h3
      exact h3
    refine le_of_tendsto' hlim (fun n => lb _ ?_ ?_ ?_)
    · have : 1 / ((n : ℝ) + 2) ≤ 1 := by
        rw [div_le_one (by positivity)]; linarith
      linarith
    · have : 0 < 1 / ((n : ℝ) + 2) := by positivity
      linarith
    · refine le_trans (Real.sqrt_le_sqrt ?_) hsa
      have : 0 < 1 / ((n : ℝ) + 2) := by positivity
      nlinarith
  · rw [min_eq_left hsa.le]
    set θ := a ^ 2 / (2 * k) with hθ
    have hsq : Real.sqrt (2 * k * θ) = a := by
      rw [hθ, show 2 * k * (a ^ 2 / (2 * k)) = a ^ 2 by field_simp]
      exact Real.sqrt_sq ha
    have hθ1 : θ < 1 := by
      rw [hθ, div_lt_one (by positivity)]
      have := Real.sq_sqrt (show (0:ℝ) ≤ 2 * k by positivity)
      nlinarith [Real.sqrt_nonneg (2 * k)]
    have := lb θ (by positivity) hθ1 hsq.le
    rwa [hsq] at this

end LostSalesRQ

open LostSalesRQ in
theorem solution (μ a k : ℝ) (hμ : 0 ≤ μ) (ha : 0 ≤ a) (hk : 0 ≤ k) :
    (∀ θ : ℝ, 0 ≤ θ → θ < 1 → Real.sqrt (2 * k * θ) ≤ a →
      ENNReal.ofReal (Real.sqrt (2 * k * θ)) +
          ENNReal.ofReal (1 - θ) * OPTk μ ((a - Real.sqrt (2 * k * θ)) / (1 - θ)) 0 ≤
        OPTk μ a k) ∧
    ENNReal.ofReal (min a (Real.sqrt (2 * k))) ≤ OPTk μ a k :=
  operating_transform' μ a k hμ ha hk
