-- Prove2me | solution 2 for LostSalesRQ.exact_base_stock_cost
-- status  : ACCEPTED   (prove)
-- author  : @Ming Hu
-- created : 2026-11-18T04:33:06.036407+00:00
-- url     : https://prove2.me/submissions/5cfe255a-cd08-4863-9d20-b0f5541a0550

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
import Theorems.Thm_LostSalesRQ_base_stock_served_rate
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.Independence.CharacteristicFunction
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


namespace LostSalesRQ

open MeasureTheory ProbabilityTheory Filter Set Topology

/-- Cumulative sales of the (r,Q) rule along the demand sequence: m k counts the demands
strictly before the arrival of demand k shifted back by the lead time. -/
def rqS (r Q : ℕ) (m : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | k + 1 => rqS r Q m k +
      if rqS r Q m k < r + Q + Q * (rqS r Q m (min (m (k + 1)) k) / Q) then 1 else 0
termination_by k => k
decreasing_by all_goals omega

lemma rqS_zero (r Q : ℕ) (m : ℕ → ℕ) : rqS r Q m 0 = 0 := by rw [rqS]

lemma rqS_succ (r Q : ℕ) (m : ℕ → ℕ) (k : ℕ) : rqS r Q m (k + 1) = rqS r Q m k +
    if rqS r Q m k < r + Q + Q * (rqS r Q m (min (m (k + 1)) k) / Q) then 1 else 0 := by
  rw [rqS]

lemma rqS_mono (r Q : ℕ) (m : ℕ → ℕ) : Monotone (rqS r Q m) :=
  monotone_nat_of_le_succ (fun k => by rw [rqS_succ]; omega)

lemma rqS_congr (r Q : ℕ) (m m' : ℕ → ℕ) (n : ℕ)
    (h : ∀ k, 1 ≤ k → k ≤ n → m k = m' k) : ∀ i ≤ n, rqS r Q m i = rqS r Q m' i := by
  induction n with
  | zero => intro i hi; rw [Nat.le_zero.mp hi, rqS_zero, rqS_zero]
  | succ n ih =>
    have ih' := ih (fun k hk1 hk2 => h k hk1 (by omega))
    intro i hi
    rcases Nat.lt_or_ge i (n + 1) with hlt | hge
    · exact ih' i (by omega)
    · have hi' : i = n + 1 := by omega
      subst hi'
      rw [rqS_succ, rqS_succ, ih' n le_rfl, h (n + 1) (by omega) le_rfl,
        ih' (min (m' (n + 1)) n) (min_le_right _ _)]

/-- Demands strictly before arrT N k - L. -/
noncomputable def mOf (L : ℝ) (N : ℝ → ℕ) (k : ℕ) : ℕ := leftLim N (arrT N k - L)

/-- Initial supply of the (r,Q) policy. -/
noncomputable def rqInit (r Q : ℕ) (t : ℝ) : ℕ := if 0 ≤ t then r + Q else 0

/-- Cumulative orders of the (r,Q) policy. -/
noncomputable def rqU (r Q : ℕ) (L : ℝ) (N : ℝ → ℕ) (t : ℝ) : ℕ :=
  Q * (rqS r Q (mOf L N) (N t) / Q)

lemma leftLim_comp_mono {g : ℕ → ℕ} (hg : Monotone g) {N : ℝ → ℕ} (hN : Monotone N) (x : ℝ) :
    leftLim (fun s => g (N s)) x = g (leftLim N x) := by
  obtain ⟨s0, hs0, he0⟩ := leftLim_attained hN x
  obtain ⟨s1, hs1, he1⟩ := leftLim_attained (fun a b hab => hg (hN hab)) x
  have hs : max s0 s1 < x := max_lt hs0 hs1
  rw [← he1 (max s0 s1) (le_max_right _ _) hs, he0 (max s0 s1) (le_max_left _ _) hs]

lemma leftLim_rqInit (r Q : ℕ) {x : ℝ} (hx : 0 < x) : leftLim (rqInit r Q) x = r + Q := by
  have hm : Monotone (rqInit r Q) := by
    intro a b hab; unfold rqInit; split_ifs <;> first | omega | (exfalso; linarith)
  obtain ⟨s0, hs0, he0⟩ := leftLim_attained hm x
  set s := max s0 (x / 2) with hs
  have h1 : s < x := max_lt hs0 (by linarith)
  rw [← he0 s (le_max_left _ _) h1]
  unfold rqInit; rw [if_pos (by have := le_max_right s0 (x / 2); linarith)]

lemma mOf_lt {L : ℝ} (hL : 0 ≤ L) {N : ℝ → ℕ} (hN : RegPath N) (h0 : ∀ s, s ≤ 0 → N s = 0)
    {k : ℕ} (hk : 1 ≤ k) {t : ℝ} (hkt : k ≤ N t) : mOf L N k < k := by
  unfold mOf
  have h1 : leftLim N (arrT N k - L) ≤ leftLim N (arrT N k) := leftLim_mono hN.1 (by linarith)
  obtain ⟨s0, hs0, he0⟩ := leftLim_attained hN.1 (arrT N k)
  have h2 : N s0 < k := by
    by_contra hc; push Not at hc
    have := (arrT_spec hN h0 hk hkt s0).mp hc
    linarith
  rw [he0 s0 le_rfl hs0] at h2
  omega

theorem rq_served (r Q : ℕ) {L : ℝ} (hL : 0 ≤ L) {N : ℝ → ℕ} (hN : RegPath N)
    (h0 : ∀ s, s ≤ 0 → N s = 0) (t : ℝ) :
    servedPath L (rqInit r Q) (rqU r Q L N) N t = rqS r Q (mOf L N) (N t) := by
  rw [servedPath_srec L _ _ N hN h0 t]
  have hg : Monotone (fun n => Q * (rqS r Q (mOf L N) n / Q)) :=
    fun a b hab => Nat.mul_le_mul_left _ (Nat.div_le_div_right (rqS_mono r Q _ hab))
  have key : ∀ n, n ≤ N t → srec (custAvail L (rqInit r Q) (rqU r Q L N) N) n =
      rqS r Q (mOf L N) n := by
    intro n
    induction n with
    | zero => intro _; rw [rqS_zero]; rfl
    | succ n ih =>
      intro hn
      have ih' := ih (by omega)
      have hcust : custAvail L (rqInit r Q) (rqU r Q L N) N (n + 1) =
          r + Q + Q * (rqS r Q (mOf L N) (min (mOf L N (n + 1)) n) / Q) := by
        unfold custAvail
        rw [leftLim_rqInit r Q (arrT_pos hN h0 (by omega) hn)]
        have hU : rqU r Q L N = fun s => (fun n => Q * (rqS r Q (mOf L N) n / Q)) (N s) := rfl
        rw [hU, leftLim_comp_mono hg hN.1]
        have := mOf_lt hL hN h0 (k := n + 1) (by omega) hn
        rw [min_eq_left (by omega)]
        rfl
      simp only [srec]
      rw [ih', hcust, rqS_succ]
  exact key (N t) le_rfl

end LostSalesRQ

namespace LostSalesRQ

open MeasureTheory ProbabilityTheory Filter Set Topology

section rqmeas
variable {lam : ℝ} (S : DemandSpace lam)

/-- Capped lead-time demand counts, relevant up to N t. -/
noncomputable def mCap (L t : ℝ) (ω : S.Ω) (k : ℕ) : ℕ :=
  if 1 ≤ k ∧ k ≤ S.N t ω then mOf L (fun s => S.N s ω) k else 0

lemma mOf_ge_iff {L : ℝ} (hL : 0 ≤ L) (ω : S.Ω) {k j : ℕ} (hk : 1 ≤ k) {t : ℝ}
    (hkt : k ≤ S.N t ω) :
    j ≤ mOf L (fun s => S.N s ω) k ↔ ∃ q : ℚ, (q : ℝ) + L < t ∧
      S.N ((q : ℝ) + L) ω < k ∧ j ≤ S.N (q : ℝ) ω := by
  have hN := S.regPath ω
  have h0 : ∀ s, s ≤ 0 → S.N s ω = 0 := fun s hs => S.N_nonpos ω s hs
  have hspec := arrT_spec hN h0 hk hkt
  have hσt := arrT_le hN h0 hk hkt
  unfold mOf
  constructor
  · intro hj
    obtain ⟨s0, hs0, he0⟩ := leftLim_attained hN.1 (arrT (fun s => S.N s ω) k - L)
    obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn hs0
    refine ⟨q, by linarith, ?_, ?_⟩
    · by_contra hc; push Not at hc
      have := (hspec _).mp hc
      linarith
    · have := he0 q hq1.le hq2
      rw [← this] at hj; exact hj
  · rintro ⟨q, _, hq2, hq3⟩
    have hlt : (q : ℝ) < arrT (fun s => S.N s ω) k - L := by
      by_contra hc; push Not at hc
      have := (hspec ((q : ℝ) + L)).mpr (by linarith)
      exact absurd this (not_le.mpr hq2)
    exact le_trans hq3 (le_leftLim hN.1 hlt)

lemma measurableSet_mCap_ge {L : ℝ} (hL : 0 ≤ L) (t : ℝ) (k j : ℕ) :
    MeasurableSet[S.𝓕 t] {ω | j ≤ mCap S L t ω k} := by
  rcases Nat.eq_zero_or_pos j with hj | hj
  · subst hj; simp
  by_cases hk : 1 ≤ k
  · have heq : {ω | j ≤ mCap S L t ω k} = {ω | k ≤ S.N t ω} ∩
        ⋃ q : ℚ, (if (q : ℝ) + L < t then {ω | S.N ((q : ℝ) + L) ω < k ∧ j ≤ S.N (q : ℝ) ω}
          else ∅) := by
      ext ω
      simp only [mem_setOf_eq, mem_inter_iff, mem_iUnion]
      unfold mCap
      constructor
      · intro h
        split_ifs at h with hc
        · refine ⟨hc.2, ?_⟩
          obtain ⟨q, hq1, hq2, hq3⟩ := (mOf_ge_iff S hL ω hk hc.2).mp h
          exact ⟨q, by rw [if_pos hq1]; exact ⟨hq2, hq3⟩⟩
        · omega
      · rintro ⟨hkt, q, hq⟩
        split_ifs at hq with hq1
        · rw [if_pos ⟨hk, hkt⟩]
          exact (mOf_ge_iff S hL ω hk hkt).mpr ⟨q, hq1, hq⟩
        · exact absurd hq (notMem_empty ω)
    rw [heq]
    refine MeasurableSet.inter ((S.N_adapted t) (MeasurableSet.of_discrete (s := {n : ℕ | k ≤ n})))
      (MeasurableSet.iUnion (fun q => ?_))
    split_ifs with hq
    · refine MeasurableSet.inter ?_ ?_
      · exact ((S.N_adapted _).mono (S.𝓕.mono hq.le) le_rfl)
          (MeasurableSet.of_discrete (s := {n : ℕ | n < k}))
      · exact ((S.N_adapted _).mono (S.𝓕.mono (by linarith)) le_rfl)
          (MeasurableSet.of_discrete (s := {n : ℕ | j ≤ n}))
    · exact @MeasurableSet.empty _ (S.𝓕 t)
  · have : {ω | j ≤ mCap S L t ω k} = ∅ := by
      ext ω; simp only [mem_setOf_eq, mem_empty_iff_false, iff_false]
      unfold mCap; rw [if_neg (by omega)]; omega
    rw [this]; exact @MeasurableSet.empty _ (S.𝓕 t)

lemma measurable_mCap {L : ℝ} (hL : 0 ≤ L) (t : ℝ) (k : ℕ) :
    Measurable[S.𝓕 t] (fun ω => mCap S L t ω k) := by
  refine @measurable_to_countable' ℕ S.Ω _ _ (S.𝓕 t) _ (fun j => ?_)
  have : (fun ω => mCap S L t ω k) ⁻¹' {j} =
      {ω | j ≤ mCap S L t ω k} \ {ω | j + 1 ≤ mCap S L t ω k} := by
    ext ω; simp only [mem_preimage, mem_singleton_iff, mem_diff, mem_setOf_eq]; omega
  rw [this]
  exact (measurableSet_mCap_ge S hL t k j).diff (measurableSet_mCap_ge S hL t k (j + 1))

lemma measurable_rqS_mCap (r Q : ℕ) {L : ℝ} (hL : 0 ≤ L) (t : ℝ) :
    ∀ n, Measurable[S.𝓕 t] (fun ω => rqS r Q (mCap S L t ω) n) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases n with _ | n
    · simp only [rqS_zero]; exact measurable_const
    · simp only [rqS_succ]
      have hn := ih n (by omega)
      have hG : ∀ i : ℕ, Measurable[S.𝓕 t] (fun ω => rqS r Q (mCap S L t ω) (min i n)) :=
        fun i => ih (min i n) (by omega)
      have hK : Measurable[S.𝓕 t] (fun ω => min (mCap S L t ω (n + 1)) n) :=
        (measurable_of_countable (fun i : ℕ => min i n)).comp (measurable_mCap S hL t (n + 1))
      have hsel := measurable_sel' (G := fun i ω => rqS r Q (mCap S L t ω) (min i n)) hG hK
      have hsel' : Measurable[S.𝓕 t] (fun ω => rqS r Q (mCap S L t ω) (min (mCap S L t ω (n + 1)) n)) := by
        convert hsel using 2 with ω
        rw [min_eq_left (min_le_right _ _)]
      exact (measurable_of_countable (fun p : ℕ × ℕ =>
          p.1 + if p.1 < r + Q + Q * (p.2 / Q) then 1 else 0)).comp (hn.prodMk hsel')

lemma measurable_rqU (r Q : ℕ) {L : ℝ} (hL : 0 ≤ L) (t : ℝ) :
    Measurable[S.𝓕 t] (fun ω => rqU r Q L (fun s => S.N s ω) t) := by
  have hsel := measurable_sel' (G := fun n ω => Q * (rqS r Q (mCap S L t ω) n / Q))
    (fun n => (measurable_of_countable (fun i : ℕ => Q * (i / Q))).comp
      (measurable_rqS_mCap S r Q hL t n)) (S.N_adapted t)
  convert hsel using 2 with ω
  unfold rqU
  rw [rqS_congr r Q (mOf L (fun s => S.N s ω)) (mCap S L t ω) (S.N t ω)
    (fun k hk1 hk2 => by unfold mCap; rw [if_pos ⟨hk1, hk2⟩]) (S.N t ω) le_rfl]

end rqmeas

theorem rq_policy_exists' (lam L : ℝ) (hlam : 0 ≤ lam) (hL : 0 ≤ L) (S : DemandSpace lam)
    (r Q : ℕ) (hQ : 1 ≤ Q) :
    ∃ π : Policy S, IsRQPolicy L r Q π := by
  have hinit_mono : Monotone (rqInit r Q) := by
    intro a b hab; unfold rqInit; split_ifs <;> first | omega | (exfalso; linarith)
  let π : Policy S :=
    { init := fun t _ => rqInit r Q t
      U := fun t ω => rqU r Q L (fun s => S.N s ω) t
      init_meas := fun _ => measurable_const
      init_nonpos := fun _ t ht => by unfold rqInit; rw [if_neg (by linarith)]
      init_mono := fun _ => hinit_mono
      init_rcont := fun _ t => by
        rcases lt_or_ge t 0 with ht | ht
        · exact ⟨-t, by linarith, fun s h1 h2 => by
            unfold rqInit; rw [if_neg (by linarith), if_neg (by linarith)]⟩
        · exact ⟨1, one_pos, fun s h1 h2 => by
            unfold rqInit; rw [if_pos (by linarith), if_pos ht]⟩
      init_bdd := fun _ => ⟨r + Q, fun t => by unfold rqInit; split_ifs <;> omega⟩
      U_adapted := fun t => measurable_rqU S r Q hL t
      U_nonpos := fun ω t ht => by
        unfold rqU; simp only [S.N_nonpos ω t ht.le, rqS_zero, Nat.zero_div, mul_zero]
      U_mono := fun ω a b hab => by
        unfold rqU
        exact Nat.mul_le_mul_left _ (Nat.div_le_div_right (rqS_mono r Q _ (S.N_mono ω hab)))
      U_rcont := fun ω t => by
        obtain ⟨δ, hδ, hc⟩ := S.N_rcont ω t
        exact ⟨δ, hδ, fun s h1 h2 => by unfold rqU; simp only [hc s h1 h2]⟩ }
  refine ⟨π, fun ω t => rfl, fun ω t => ?_⟩
  show rqU r Q L (fun s => S.N s ω) t = Q * (servedPath L (rqInit r Q)
    (fun s => rqU r Q L (fun s => S.N s ω) s) (fun s => S.N s ω) t / Q)
  rw [rq_served r Q hL (S.regPath ω) (fun s hs => S.N_nonpos ω s hs) t]
  rfl

end LostSalesRQ


namespace LostSalesRQ.TBE
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


lemma R_ineq {μ : ℝ} (hμ : 0 < μ) (j : ℕ) :
    μ ≤ (meanOnHand μ j + 1) * (meanOnHand μ j + μ * lossFraction μ j) := by
  induction j with
  | zero =>
    have h0 : lossFraction μ 0 = 1 := by
      unfold lossFraction; rw [pc_zero]; exact div_self (pm_pos hμ 0).ne'
    have hH0 : meanOnHand μ 0 = 0 := by unfold meanOnHand; rw [h0]; simp
    rw [hH0, h0]; linarith
  | succ n ih =>
    have he := lf_pos hμ n
    have hH := moh_nonneg hμ n
    have hrec := lf_succ hμ n
    have hHdef : meanOnHand μ n = (n : ℝ) - μ + μ * lossFraction μ n := rfl
    have hH' : meanOnHand μ (n + 1) = ((n : ℝ) + 1) - μ + μ * lossFraction μ (n + 1) := by
      unfold meanOnHand; push_cast; ring
    rw [hH', hrec]
    set e := lossFraction μ n with he_def
    set H := meanOnHand μ n with hH_def
    have heH : μ * e = H - n + μ := by linarith [hHdef]
    have hD : 0 < μ + H + 1 := by linarith
    have hsub : μ * (μ * e / (μ + H + 1)) = μ * (H - n + μ) / (μ + H + 1) := by
      rw [← heH]; ring
    rw [hsub, ← sub_nonneg]
    have key : ((n : ℝ) + 1 - μ + μ * (H - n + μ) / (μ + H + 1) + 1) *
        ((n : ℝ) + 1 - μ + μ * (H - n + μ) / (μ + H + 1) + μ * (H - n + μ) / (μ + H + 1)) - μ
        = ((n : ℝ) + 1) * ((H + 1) ^ 2 * ((n : ℝ) + 2 + μ) + (H + 1) * μ * (μ - n - 1) - μ ^ 2)
            / (μ + H + 1) ^ 2 := by
      field_simp; ring
    rw [key]
    apply div_nonneg _ (by positivity)
    apply mul_nonneg (by positivity)
    have hR : 0 ≤ (H + 1) * (2 * H - n + μ) - μ := by
      have : (H + 1) * (H + μ * e) = (H + 1) * (2 * H - n + μ) := by rw [heH]; ring
      linarith [ih, this]
    have ha : 0 < H + 1 := by linarith
    by_cases hc : 0 ≤ (H + 1) * ((n : ℝ) + 2 - μ) + μ
    · nlinarith [mul_nonneg hμ.le hR, mul_nonneg ha.le hc]
    · push_neg at hc
      have hc' : 0 < (H + 1) * (μ - n - 2) - μ := by linarith
      have hm : 0 < μ - n - 2 := by
        by_contra hneg; push_neg at hneg
        nlinarith [mul_nonneg ha.le (by linarith : (0 : ℝ) ≤ -(μ - n - 2))]
      have h1 : 0 < μ * ((H + 1) * (μ - n - 2) - μ) := mul_pos hμ hc'
      have h2 : 0 < (H + 1) ^ 2 * ((n : ℝ) + 2 + μ) := by positivity
      have h3 : 0 < (H + 1) * μ := mul_pos ha hμ
      nlinarith [h1, h2, h3]


theorem var_bound (μ : ℝ) (hμ : 0 < μ) (j : ℕ) (hj : 1 ≤ j) :
    0 < onHandVariance μ j ∧ onHandVariance μ j ≤ meanOnHand μ j * (meanOnHand μ j + 1) := by
  constructor
  · have hF := pc_pos hμ j
    have hsub : ({0, 1} : Finset ℕ) ⊆ Finset.range (j + 1) := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      simp only [Finset.mem_range]
      omega
    have hnn : ∀ l ∈ Finset.range (j + 1),
        0 ≤ ((l : ℝ) - meanOnHand μ j) ^ 2 * (poisMass μ (j - l) / poisCdf μ j) := by
      intro l _
      exact mul_nonneg (sq_nonneg _) (div_nonneg (pm_pos hμ _).le hF.le)
    have hle := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun l hl _ => hnn l hl)
    rw [Finset.sum_pair (by norm_num)] at hle
    simp only [Nat.cast_zero, Nat.cast_one, Nat.sub_zero] at hle
    have hw0 : 0 < poisMass μ j / poisCdf μ j := div_pos (pm_pos hμ _) hF
    have hw1 : 0 < poisMass μ (j - 1) / poisCdf μ j := div_pos (pm_pos hμ _) hF
    set H := meanOnHand μ j
    have hpos : 0 < (0 - H) ^ 2 * (poisMass μ j / poisCdf μ j)
        + (1 - H) ^ 2 * (poisMass μ (j - 1) / poisCdf μ j) := by
      by_cases hH0 : H = 0
      · rw [hH0]; norm_num; exact hw1
      · have : 0 < (0 - H) ^ 2 := by
          have : (0 - H) ≠ 0 := by intro h; apply hH0; linarith
          positivity
        nlinarith [mul_pos this hw0, mul_nonneg (sq_nonneg (1 - H)) hw1.le]
    unfold onHandVariance
    linarith
  · have hR := R_ineq hμ j
    have hv := ohv_eq hμ j
    rw [hv]
    nlinarith [hR]

end LostSalesRQ.TBE

namespace LostSalesRQ

open TBE

theorem tb_part2 (μ a : ℝ) (ha : 0 < a) (haμ : a < μ) (j : ℕ) :
    2 * Real.sqrt (a * (1 - a / μ)) - (1 - a / μ) ≤ baseStockCost μ a j := by
  have hμ : 0 < μ := lt_trans ha haμ
  set ω := 1 - a / μ with hω
  have hω0 : 0 < ω := by rw [hω, sub_pos, div_lt_one hμ]; exact haμ
  set H := meanOnHand μ j with hH
  set e := lossFraction μ j with he
  have hH0 : 0 ≤ H := moh_nonneg hμ j
  have hv : onHandVariance μ j ≤ H * (H + 1) := by
    rcases Nat.eq_zero_or_pos j with hj | hj
    · subst hj
      have he0 : lossFraction μ 0 = 1 := by
        unfold lossFraction; rw [pc_zero]; exact div_self (pm_pos hμ 0).ne'
      have hH0' : meanOnHand μ 0 = 0 := by unfold meanOnHand; rw [he0]; simp
      unfold onHandVariance
      simp only [hH0', Finset.sum_range_one, Nat.cast_zero, sub_zero]
      simp [hH]
      rw [hH0']; simp
    · exact (var_bound μ hμ j hj).2
  have hvar := ohv_eq hμ j
  rw [← hH, ← he] at hvar
  -- e (H+1) ≥ 1 - H(H+1)/μ
  have hkey : 1 - H * (H + 1) / μ ≤ e * (H + 1) := by
    have : μ * (1 - e * (H + 1)) ≤ H * (H + 1) := by rw [← hvar]; exact hv
    have h1 : 1 - e * (H + 1) ≤ H * (H + 1) / μ := by rw [le_div_iff₀ hμ]; linarith
    linarith
  have he_lb : 1 / (H + 1) - H / μ ≤ e := by
    have hH1 : 0 < H + 1 := by linarith
    have h2 : 1 / (H + 1) - H / μ = (1 - H * (H + 1) / μ) / (H + 1) := by field_simp
    rw [h2, div_le_iff₀ hH1]; linarith
  have hL : ω * (H + 1) + a / (H + 1) - ω ≤ baseStockCost μ a j := by
    unfold baseStockCost
    rw [← hH, ← he]
    have : a * (1 / (H + 1) - H / μ) ≤ a * e := mul_le_mul_of_nonneg_left he_lb ha.le
    have h2 : a * (1 / (H + 1) - H / μ) = a / (H + 1) - a / μ * H := by ring
    rw [hω]; nlinarith
  have hamgm : 2 * Real.sqrt (a * ω) ≤ ω * (H + 1) + a / (H + 1) := by
    set x := H + 1 with hx
    have hx0 : 0 < x := by linarith
    set s := Real.sqrt (a * ω) with hs
    have hs2 : s ^ 2 = a * ω := Real.sq_sqrt (by positivity)
    have : 0 ≤ (ω * x - s) ^ 2 / (ω * x) := by positivity
    have h3 : (ω * x - s) ^ 2 / (ω * x) = ω * x + a / x - 2 * s := by
      field_simp
      linear_combination hs2
    linarith
  linarith

end LostSalesRQ

namespace LostSalesRQ

open MeasureTheory ProbabilityTheory Filter Set Topology

/-- Cumulative unit orders placed at times 0, 1/ρ, 2/ρ, ... -/
noncomputable def tbU (ρ t : ℝ) : ℕ := if t < 0 then 0 else ⌊ρ * t⌋₊ + 1

lemma tbU_mono {ρ : ℝ} (hρ : 0 < ρ) : Monotone (tbU ρ) := by
  intro a b hab
  unfold tbU
  split_ifs with ha hb hb
  · exact le_rfl
  · exact Nat.zero_le _
  · exfalso; linarith
  · exact Nat.add_le_add_right (Nat.floor_le_floor (by nlinarith)) 1

lemma tbU_rcont {ρ : ℝ} (hρ : 0 < ρ) (t : ℝ) :
    ∃ δ > 0, ∀ s, t ≤ s → s < t + δ → tbU ρ s = tbU ρ t := by
  rcases lt_or_ge t 0 with ht | ht
  · refine ⟨-t, by linarith, fun s h1 h2 => ?_⟩
    unfold tbU; rw [if_pos (by linarith), if_pos ht]
  · set n := ⌊ρ * t⌋₊ with hn
    have h1 : ρ * t < n + 1 := Nat.lt_floor_add_one _
    refine ⟨(n + 1 - ρ * t) / ρ, div_pos (by linarith) hρ, fun s hs1 hs2 => ?_⟩
    unfold tbU
    rw [if_neg (by linarith), if_neg (by linarith)]
    congr 1
    rw [Nat.floor_eq_iff (by nlinarith)]
    constructor
    · have : (n : ℝ) ≤ ρ * t := Nat.floor_le (by nlinarith)
      nlinarith
    · have : ρ * s < ρ * (t + (n + 1 - ρ * t) / ρ) := mul_lt_mul_of_pos_left hs2 hρ
      rw [mul_add, mul_div_cancel₀ _ hρ.ne'] at this
      linarith

lemma tbU_gt (ρ y : ℝ) (hρ : 0 < ρ) : ρ * y < tbU ρ y := by
  unfold tbU
  split_ifs with h
  · simp; nlinarith
  · push_cast; exact Nat.lt_floor_add_one _

lemma tbU_le (ρ y : ℝ) (hρ : 0 < ρ) (hy : 0 ≤ y) : (tbU ρ y : ℝ) ≤ ρ * y + 1 := by
  unfold tbU; rw [if_neg (by linarith)]; push_cast
  linarith [Nat.floor_le (show 0 ≤ ρ * y by positivity)]

lemma tbU_le' (ρ y : ℝ) (hρ : 0 < ρ) : (tbU ρ y : ℝ) ≤ ρ * max y 0 + 1 := by
  rcases lt_or_ge y 0 with h | h
  · unfold tbU; rw [if_pos h]; simp; positivity
  · rw [max_eq_left h]; exact tbU_le ρ y hρ h

lemma tbU_epoch {ρ : ℝ} (hρ : 0 < ρ) (y : ℝ) (h : leftLim (tbU ρ) y < tbU ρ y) :
    (leftLim (tbU ρ) y : ℝ) = ρ * y ∧ tbU ρ y = leftLim (tbU ρ) y + 1 := by
  have hm := tbU_mono hρ
  obtain ⟨s0, hs0, he0⟩ := leftLim_attained hm y
  set m := leftLim (tbU ρ) y with hmdef
  rcases lt_or_ge y 0 with hy | hy
  · exfalso; unfold tbU at h; rw [if_pos hy] at h; omega
  rcases eq_or_lt_of_le hy with hy0 | hypos
  · subst hy0
    have : m = 0 := by
      rw [← he0 s0 le_rfl hs0]; unfold tbU; rw [if_pos hs0]
    refine ⟨by rw [this]; simp, ?_⟩
    rw [this]; unfold tbU; simp
  · have hval : tbU ρ y = ⌊ρ * y⌋₊ + 1 := by unfold tbU; rw [if_neg (by linarith)]
    set s1 := max s0 0 with hs1
    have hs1y : s1 < y := max_lt hs0 hypos
    have hup : ρ * y ≤ m := by
      by_contra hc; push Not at hc
      set s := max s1 (y - (ρ * y - m) / (2 * ρ)) with hs
      have hsy : s < y := max_lt hs1y (by
        have : 0 < (ρ * y - m) / (2 * ρ) := div_pos (by linarith) (by positivity)
        linarith)
      have hs_ge : s1 ≤ s := le_max_left _ _
      have hms : tbU ρ s = m := he0 s (le_trans (le_max_left _ _) hs_ge) hsy
      have hlt := tbU_gt ρ s hρ
      rw [hms] at hlt
      have h3 : ρ * (y - (ρ * y - m) / (2 * ρ)) ≤ ρ * s :=
        mul_le_mul_of_nonneg_left (le_max_right _ _) hρ.le
      have h4 : ρ * (y - (ρ * y - m) / (2 * ρ)) = ρ * y - (ρ * y - m) / 2 := by
        field_simp
      linarith
    have hlo : (m : ℝ) ≤ ρ * y := by
      have h2 : m ≤ ⌊ρ * y⌋₊ := by rw [hval] at h; omega
      exact le_trans (by exact_mod_cast h2) (Nat.floor_le (by positivity))
    have heq : (m : ℝ) = ρ * y := le_antisymm hlo hup
    refine ⟨heq, ?_⟩
    rw [hval, ← heq, Nat.floor_natCast]

/-- Deterministic holding offset: ∫ (D - ρ (t - μ)) ≤ T/2 + const. -/
theorem tb_det_int {ρ : ℝ} (hρ : 0 < ρ) (μ T : ℝ) (hμ : 0 ≤ μ) (hT : 0 ≤ T) :
    IntervalIntegrable (fun t => (tbU ρ (t - μ) : ℝ) - ρ * (t - μ)) volume 0 T ∧
    ∫ t in (0:ℝ)..T, ((tbU ρ (t - μ) : ℝ) - ρ * (t - μ)) ≤ T / 2 + ρ * μ ^ 2 / 2 + 1 / (2 * ρ) := by
  set D : ℝ → ℕ := fun t => tbU ρ (t - μ) with hD
  have hDr : RegPath D := regPath_shift ⟨tbU_mono hρ, tbU_rcont hρ⟩ μ
  have hfc : ∀ ξ : ℕ, Continuous (fun t : ℝ => (ξ : ℝ) - ρ * (t - μ)) := fun ξ => by fun_prop
  have hFd : ∀ (ξ : ℕ) (t : ℝ), HasDerivAt
      (fun t : ℝ => (ξ : ℝ) * (t - μ) - ρ * (t - μ) ^ 2 / 2 - (ξ : ℝ) * (ξ - 1) / (2 * ρ))
      ((ξ : ℝ) - ρ * (t - μ)) t := by
    intro ξ t
    have h1 := ((hasDerivAt_id t).sub_const μ).const_mul (ξ : ℝ)
    have h2 := (((hasDerivAt_id t).sub_const μ).pow 2).const_mul ρ |>.div_const 2
    have := (h1.sub h2).sub_const ((ξ : ℝ) * (ξ - 1) / (2 * ρ))
    exact this.congr_deriv (by simp only [id]; push_cast; ring)
  set F : ℕ → ℝ → ℝ := fun ξ t => ξ * (t - μ) - ρ * (t - μ) ^ 2 / 2 - (ξ : ℝ) * (ξ - 1) / (2 * ρ)
    with hF
  set f : ℕ → ℝ → ℝ := fun ξ t => ξ - ρ * (t - μ) with hf
  set E := (epochSet_finite hDr.1 T).toFinset with hE
  have hEmem : ∀ e ∈ E, 0 < e ∧ e ≤ T := fun e he => ((Set.Finite.mem_toFinset _).mp he).1
  have hpw := piecewise_ftc F f
    (fun ξ a b hab => (intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hFd ξ t)
      ((hfc ξ).intervalIntegrable a b)).symm)
    (fun ξ a b => (hfc ξ).intervalIntegrable a b)
    D (leftLim D) E T hT hEmem
    (fun s t hs hst htT hno => const_of_noEpoch hDr hs hst (fun τ h1 h2 h3 =>
      hno τ ((Set.Finite.mem_toFinset _).mpr ⟨⟨by linarith, le_trans h2 htT⟩, h3⟩) ⟨h1, h2⟩))
    (fun e _ => by
      obtain ⟨s0, hs0, he0⟩ := leftLim_attained hDr.1 e
      exact ⟨e - s0, by linarith, fun s h1 h2 => he0 s (by linarith) h2⟩)
  obtain ⟨hii, hid⟩ := hpw
  have hjump : ∀ e ∈ E, F (D e) e - F (leftLim D e) e = 0 := by
    intro e he
    have he' := ((Set.Finite.mem_toFinset _).mp he).2
    have hl : leftLim D e = leftLim (tbU ρ) (e - μ) := leftLim_shift (tbU ρ) μ e
    have hep : leftLim (tbU ρ) (e - μ) < tbU ρ (e - μ) := by rw [← hl]; exact he'
    obtain ⟨h1, h2⟩ := tbU_epoch hρ (e - μ) hep
    simp only [hF, hD]
    rw [hl, h2]
    push_cast
    rw [h1]
    field_simp
    ring
  rw [Finset.sum_eq_zero hjump, add_zero] at hid
  refine ⟨hii, ?_⟩
  have hint : ∫ t in (0:ℝ)..T, ((tbU ρ (t - μ) : ℝ) - ρ * (t - μ)) = F (D T) T - F (D 0) 0 := by
    rw [hid]
  rw [hint]
  have hF0 : F (D 0) 0 = -(ρ * μ ^ 2 / 2) := by
    simp only [hF, hD, zero_sub]
    rcases eq_or_lt_of_le hμ with h0 | hpos
    · subst h0; unfold tbU; simp
    · unfold tbU; rw [if_pos (by linarith)]; simp
  rw [hF0]
  simp only [hF, hD]
  rcases lt_or_ge T μ with hTμ | hTμ
  · rw [show tbU ρ (T - μ) = 0 by unfold tbU; rw [if_pos (by linarith)]]
    push_cast
    have h5 : 0 ≤ 1 / (2 * ρ) := by positivity
    have h6 : 0 ≤ ρ * (T - μ) ^ 2 := mul_nonneg hρ.le (sq_nonneg (T - μ))
    have h7 : (0:ℝ) * (T - μ) - ρ * (T - μ) ^ 2 / 2 - 0 * (0 - 1) / (2 * ρ) - -(ρ * μ ^ 2 / 2) =
        ρ * μ ^ 2 / 2 - ρ * (T - μ) ^ 2 / 2 := by ring
    rw [h7]; linarith
  · set y := ρ * (T - μ) with hy
    have hy0 : 0 ≤ y := by positivity
    have hM := tbU_le ρ (T - μ) hρ (by linarith)
    have hM' := tbU_gt ρ (T - μ) hρ
    set M : ℝ := (tbU ρ (T - μ) : ℝ) with hMdef
    have key : M * (T - μ) - ρ * (T - μ) ^ 2 / 2 - M * (M - 1) / (2 * ρ) =
        (M - (M - y) ^ 2) / (2 * ρ) := by
      rw [hy]; field_simp; ring
    rw [key]
    have : (M - (M - y) ^ 2) / (2 * ρ) ≤ M / (2 * ρ) :=
      div_le_div_of_nonneg_right (by nlinarith) (by positivity)
    have h2 : M / (2 * ρ) ≤ (y + 1) / (2 * ρ) := div_le_div_of_nonneg_right (by linarith) (by positivity)
    have h3 : (y + 1) / (2 * ρ) = (T - μ) / 2 + 1 / (2 * ρ) := by rw [hy]; field_simp
    have : 0 ≤ ρ * μ ^ 2 / 2 := by positivity
    linarith

end LostSalesRQ

namespace LostSalesRQ

open MeasureTheory ProbabilityTheory Filter Set Topology

/-- The open-loop policy ordering one unit at times 0, 1/ρ, 2/ρ, ... from an empty system. -/
noncomputable def tbPolicy (S : DemandSpace 1) (ρ : ℝ) (hρ : 0 < ρ) : Policy S where
  init := fun _ _ => 0
  U := fun t _ => tbU ρ t
  init_meas := fun _ => measurable_const
  init_nonpos := fun _ _ _ => rfl
  init_mono := fun _ => monotone_const
  init_rcont := fun _ _ => ⟨1, one_pos, fun _ _ _ => rfl⟩
  init_bdd := fun _ => ⟨0, fun _ => le_rfl⟩
  U_adapted := fun _ => measurable_const
  U_nonpos := fun _ t ht => by unfold tbU; rw [if_pos ht]
  U_mono := fun _ => tbU_mono hρ
  U_rcont := fun _ t => tbU_rcont hρ t

lemma tbPolicy_empty (S : DemandSpace 1) (ρ : ℝ) (hρ : 0 < ρ) : (tbPolicy S ρ hρ).EmptyStart :=
  fun _ _ => rfl

/-- Clamp to [-C, C]. -/
noncomputable def clampC (C x : ℝ) : ℝ := max (-C) (min C x)

lemma clampC_cont (C : ℝ) : Continuous (clampC C) := by unfold clampC; fun_prop

lemma clampC_of_abs {C x : ℝ} (h : |x| ≤ C) : clampC C x = x := by
  unfold clampC; rw [abs_le] at h
  rw [min_eq_right h.2, max_eq_right h.1]

lemma abs_clampC_le {C : ℝ} (hC : 0 ≤ C) (x : ℝ) : |clampC C x| ≤ C := by
  unfold clampC; rw [abs_le]; constructor
  · exact le_max_left _ _
  · exact max_le (by linarith) (min_le_left _ _)

/-- Jump integrand of Z² at a served demand, clamped. -/
noncomputable def G1c (ρ μ C : ℝ) (a v : ℕ) (t : ℝ) : ℝ :=
  (if a < v then 1 else 0) * (1 - 2 * clampC C (ρ * (t - μ) - a))

lemma G1c_cont (ρ μ C : ℝ) (a v : ℕ) : Continuous (G1c ρ μ C a v) := by
  unfold G1c; exact continuous_const.mul (continuous_const.sub
    (continuous_const.mul ((clampC_cont C).comp (by fun_prop))))

lemma G1c_bdd {C : ℝ} (hC : 0 ≤ C) (ρ μ : ℝ) (a v : ℕ) (t : ℝ) : |G1c ρ μ C a v t| ≤ 1 + 2 * C := by
  unfold G1c
  have := abs_clampC_le hC (ρ * (t - μ) - a)
  split_ifs
  · rw [one_mul]
    calc |1 - 2 * clampC C (ρ * (t - μ) - a)| ≤ |(1:ℝ)| + |2 * clampC C (ρ * (t - μ) - a)| :=
          abs_sub _ _
      _ ≤ 1 + 2 * C := by rw [abs_one, abs_mul, abs_two]; linarith
  · simp; linarith

section tbpath
variable {μ : ℝ} {N U : ℝ → ℕ}

/-- Time-dependent state functional along the path. -/
noncomputable def GpathT (G : ℕ → ℕ → ℝ → ℝ) (μ : ℝ) (N U : ℝ → ℕ) (t : ℝ) : ℝ :=
  G (vA μ N U t) (U (t - μ)) t

lemma GpathT_left (G : ℕ → ℕ → ℝ → ℝ) (hG : ∀ a v, Continuous (G a v)) (h : PathOK μ N U)
    (t : ℝ) : Tendsto (GpathT G μ N U) (𝓝[<] t)
      (𝓝 (G (vS μ N U (leftLim N t)) (leftLim U (t - μ)) t)) := by
  obtain ⟨s1, hs1, he1⟩ := leftLim_attained h.hN.1 t
  obtain ⟨s3, hs3, he3⟩ := leftLim_attained h.hU.1 (t - μ)
  set s0 := max s1 (s3 + μ) with hs0
  have hs0t : s0 < t := max_lt hs1 (by linarith)
  refine Tendsto.congr' ?_ (((hG (vS μ N U (leftLim N t)) (leftLim U (t - μ))).tendsto t).mono_left
    nhdsWithin_le_nhds)
  filter_upwards [Ioo_mem_nhdsLT hs0t] with s hs
  have h1 : s1 ≤ s := le_trans (le_max_left _ _) hs.1.le
  have h3 : s3 + μ ≤ s := le_trans (le_max_right _ _) hs.1.le
  unfold GpathT vA
  rw [he1 s h1 hs.2, he3 (s - μ) (by linarith) (by linarith [hs.2])]

lemma GpathT_left_ae (G : ℕ → ℕ → ℝ → ℝ) (hG : ∀ a v, Continuous (G a v)) (h : PathOK μ N U)
    (T : ℝ) :
    ∀ᵐ t ∂volume, t ∈ Ioc 0 T → Tendsto (GpathT G μ N U) (𝓝[<] t) (𝓝 (GpathT G μ N U t)) := by
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
  have := GpathT_left G hG h t
  rw [hlN, hlUμ] at this
  exact this

lemma vA_zero (h : PathOK μ N U) : vA μ N U 0 = 0 := by
  unfold vA; rw [h.hN0 0 le_rfl]; simp [vS, srec]

/-- Pathwise identity for Z² with Z = ρ(t-μ) - A(t). -/
theorem tb_pathwise (ρ C : ℝ) (h : PathOK μ N U) {T : ℝ} (hT : 0 < T)
    (hgood : ∀ τ, 0 < τ → τ ≤ T → N τ ≤ leftLim N τ + 1)
    (hC : ∀ k, 1 ≤ k → k ≤ N T → vS μ N U (k - 1) < vAv μ N U k →
      |ρ * (arrT N k - μ) - vS μ N U (k - 1)| ≤ C) :
    IntervalIntegrable (fun t => 2 * ρ * (ρ * (t - μ) - vA μ N U t)) volume 0 T ∧
    (ρ * (T - μ) - vA μ N U T) ^ 2 - (ρ * μ) ^ 2 =
      (∫ t in (0:ℝ)..T, 2 * ρ * (ρ * (t - μ) - vA μ N U t)) +
      ∑ k ∈ Finset.Icc 1 (N T), G1c ρ μ C (vS μ N U (leftLim N (arrT N k))) (vAv μ N U k) (arrT N k) := by
  set EN := (epochSet_finite h.hN.1 T).toFinset with hEN
  have hEmem : ∀ e ∈ EN, 0 < e ∧ e ≤ T := fun e he => ((Set.Finite.mem_toFinset _).mp he).1
  have hFd : ∀ (ξ : ℕ) (t : ℝ), HasDerivAt (fun t : ℝ => (ρ * (t - μ) - ξ) ^ 2)
      (2 * ρ * (ρ * (t - μ) - ξ)) t := by
    intro ξ t
    have := ((((hasDerivAt_id t).sub_const μ).const_mul ρ).sub_const (ξ : ℝ)).pow 2
    exact this.congr_deriv (by simp only [id]; push_cast; ring)
  have hfc : ∀ ξ : ℕ, Continuous (fun t : ℝ => 2 * ρ * (ρ * (t - μ) - ξ)) := fun ξ => by fun_prop
  have hpw := piecewise_ftc (X := ℕ) (fun ξ t => (ρ * (t - μ) - ξ) ^ 2)
    (fun ξ t => 2 * ρ * (ρ * (t - μ) - ξ))
    (fun ξ a b hab => (intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hFd ξ t)
      ((hfc ξ).intervalIntegrable a b)).symm)
    (fun ξ a b => (hfc ξ).intervalIntegrable a b)
    (fun t => vA μ N U t) (fun e => vS μ N U (leftLim N e)) EN T hT.le hEmem
    (by
      intro s t hs hst htT hno
      have hN' : N t = N s := const_of_noEpoch h.hN hs hst (fun τ h1 h2 h3 =>
        hno τ ((Set.Finite.mem_toFinset _).mpr ⟨⟨by linarith, le_trans h2 htT⟩, h3⟩) ⟨h1, h2⟩)
      simp only [vA, hN'])
    (by
      intro e _
      obtain ⟨s1, hs1, he1⟩ := leftLim_attained h.hN.1 e
      exact ⟨e - s1, by linarith, fun s h1' h2' => by
        simp only [vA]; rw [he1 s (by linarith) h2']⟩)
  obtain ⟨hii, hpot⟩ := hpw
  refine ⟨hii, ?_⟩
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
  have hsum : ∑ e ∈ EN, ((ρ * (e - μ) - (vA μ N U e : ℝ)) ^ 2 -
      (ρ * (e - μ) - (vS μ N U (leftLim N e) : ℝ)) ^ 2) = ∑ k ∈ Finset.Icc 1 (N T),
      G1c ρ μ C (vS μ N U (leftLim N (arrT N k))) (vAv μ N U k) (arrT N k) := by
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
      have hk1 : 1 ≤ N e := by omega
      have hkT : N e ≤ N T := h.hN.1 he'.1.2
      simp only [hσ, vA, hl]
      have hsucc : vS μ N U (N e) = vS μ N U (N e - 1) +
          if vS μ N U (N e - 1) < vAv μ N U (N e) then 1 else 0 := by
        unfold vS
        conv_lhs => rw [show N e = (N e - 1) + 1 by omega]
        simp only [srec]
        rw [show N e - 1 + 1 = N e by omega]
      rw [hsucc]
      unfold G1c
      split_ifs with hlt
      · have hb := hC (N e) hk1 hkT hlt
        rw [hσ] at hb
        rw [clampC_of_abs hb]
        push_cast; ring
      · simp
  rw [← hsum]
  have h0 : vA μ N U 0 = 0 := vA_zero h
  simp only [h0, Nat.cast_zero, sub_zero, zero_sub] at hpot
  have : (-(ρ * μ)) ^ 2 = (ρ * μ) ^ 2 := by ring
  rw [show ρ * -μ = -(ρ * μ) by ring, this] at hpot
  linarith

end tbpath

end LostSalesRQ

namespace LostSalesRQ

open MeasureTheory ProbabilityTheory Filter Set Topology

section tbgen
variable {μ : ℝ} {N U : ℝ → ℕ}

lemma leftLim_arrT_good (h : PathOK μ N U) {T : ℝ}
    (hgood : ∀ τ, 0 < τ → τ ≤ T → N τ ≤ leftLim N τ + 1) {k : ℕ} (hk1 : 1 ≤ k) (hkT : k ≤ N T) :
    leftLim N (arrT N k) = k - 1 := by
  have hσ0 := arrT_pos h.hN h.hN0 hk1 hkT
  have hσT := arrT_le h.hN h.hN0 hk1 hkT
  have h1 := (arrT_spec h.hN h.hN0 hk1 hkT (arrT N k)).mpr le_rfl
  have h2 : leftLim N (arrT N k) < k := by
    obtain ⟨s0, hs0, he0⟩ := leftLim_attained h.hN.1 (arrT N k)
    rw [← he0 s0 le_rfl hs0]
    by_contra hc; push Not at hc
    have := (arrT_spec h.hN h.hN0 hk1 hkT s0).mp hc
    linarith
  have := hgood _ hσ0 hσT
  omega

lemma vA_sumG2 (h : PathOK μ N U) {T : ℝ}
    (hgood : ∀ τ, 0 < τ → τ ≤ T → N τ ≤ leftLim N τ + 1) :
    (vA μ N U T : ℝ) = ∑ k ∈ Finset.Icc 1 (N T),
      G2 (vS μ N U (leftLim N (arrT N k))) (vAv μ N U k) := by
  unfold vA; rw [vS_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have hk' := Finset.mem_Icc.mp hk
  rw [leftLim_arrT_good h hgood hk'.1 hk'.2]

lemma measurable_GpathT_time (G : ℕ → ℕ → ℝ → ℝ) (hG : ∀ a v, Continuous (G a v))
    (h : PathOK μ N U) : Measurable (GpathT G μ N U) := by
  unfold GpathT
  have hvAm : Measurable (vA μ N U) := (measurable_from_nat (f := vS μ N U)).comp h.hN.1.measurable
  have hUmu : Measurable (fun t => U (t - μ)) := h.hU.1.measurable.comp (measurable_id.sub_const μ)
  have hJ : Measurable (fun p : ℝ × (ℕ × ℕ) => G p.2.1 p.2.2 p.1) :=
    measurable_from_prod_countable_left (f := fun p : ℝ × (ℕ × ℕ) => G p.2.1 p.2.2 p.1)
      (fun b => (hG b.1 b.2).measurable)
  exact hJ.comp (measurable_id.prodMk (hvAm.prodMk hUmu))

end tbgen

/-- Served count of the open-loop policy. -/
noncomputable def tbA (S : DemandSpace 1) (ρ : ℝ) (hρ : 0 < ρ) (μ : ℝ) (ω : S.Ω) (t : ℝ) : ℕ :=
  vA μ (fun s => S.N s ω) (fun s => (tbPolicy S ρ hρ).U s ω) t

section tbexp
variable (S : DemandSpace 1) {ρ : ℝ} (hρ : 0 < ρ)

lemma tbA_le (μ : ℝ) (hμ : 0 ≤ μ) (ω : S.Ω) {t T : ℝ} (htT : t ≤ T) (hT : 0 ≤ T) :
    (tbA S ρ hρ μ ω t : ℝ) ≤ tbU ρ (t - μ) ∧ (tbU ρ (t - μ) : ℝ) ≤ ρ * T + 1 := by
  have h := (tbPolicy S ρ hρ).pathOK S μ hμ ω
  constructor
  · exact_mod_cast vA_le h t
  · refine le_trans (tbU_le' ρ (t - μ) hρ) ?_
    have : max (t - μ) 0 ≤ T := max_le (by linarith) hT
    nlinarith

lemma measurable_tbA (μ : ℝ) (hμ : 0 ≤ μ) (t : ℝ) :
    Measurable (fun ω => (tbA S ρ hρ μ ω t : ℝ)) :=
  (measurable_from_nat (f := fun n : ℕ => (n : ℝ))).comp
    ((measurable_vA S (tbPolicy S ρ hρ) μ hμ t).mono (S.𝓕.le t) le_rfl)

lemma integrable_of_bdd' {f : S.Ω → ℝ} (hf : Measurable f) {C : ℝ} (hb : ∀ ω, |f ω| ≤ C) :
    Integrable f S.ν :=
  Integrable.of_bound (C := C) hf.aestronglyMeasurable (Eventually.of_forall (fun ω => by
    rw [Real.norm_eq_abs]; exact hb ω))

/-- Drift inequality for Z = ρ(t-μ) - A(t). -/
theorem tb_drift (hρ1 : ρ < 1) (μ : ℝ) (hμ : 0 ≤ μ) {T : ℝ} (hT : 0 < T) :
    Integrable (fun ω => ∫ t in (0:ℝ)..T, (ρ * (t - μ) - tbA S ρ hρ μ ω t)) S.ν ∧
    Integrable (fun ω => (ρ * (T - μ) - tbA S ρ hρ μ ω T) ^ 2) S.ν ∧
    Integrable (fun ω => (tbA S ρ hρ μ ω T : ℝ)) S.ν ∧
    ∫ ω, (ρ * (T - μ) - tbA S ρ hρ μ ω T) ^ 2 ∂S.ν ≤
      (ρ * μ) ^ 2 - 2 * (1 - ρ) * ∫ ω, (∫ t in (0:ℝ)..T, (ρ * (t - μ) - tbA S ρ hρ μ ω t)) ∂S.ν +
        ∫ ω, (tbA S ρ hρ μ ω T : ℝ) ∂S.ν := by
  set P := tbPolicy S ρ hρ with hP
  set C := 2 * ρ * T + ρ * μ + 1 with hCdef
  have hC0 : 0 ≤ C := by positivity
  -- uniform bound on Z over [0, T]
  have hZb : ∀ ω t, 0 ≤ t → t ≤ T → |ρ * (t - μ) - (tbA S ρ hρ μ ω t : ℝ)| ≤ C := by
    intro ω t ht0 htT
    obtain ⟨h1, h2⟩ := tbA_le S hρ μ hμ ω htT hT.le
    have h3 : (0:ℝ) ≤ tbA S ρ hρ μ ω t := Nat.cast_nonneg _
    rw [abs_le]; constructor <;> nlinarith
  have hZii : ∀ ω, IntervalIntegrable (fun t => ρ * (t - μ) - (tbA S ρ hρ μ ω t : ℝ)) volume 0 T := by
    intro ω
    have h := P.pathOK S μ hμ ω
    have hmono : Monotone (fun t => (tbA S ρ hρ μ ω t : ℝ)) := by
      intro a b hab
      have := srec_mono (vAv μ (fun s => S.N s ω) (fun s => P.U s ω)) (h.hN.1 hab)
      show ((vS μ _ _ (S.N a ω) : ℕ) : ℝ) ≤ ((vS μ _ _ (S.N b ω) : ℕ) : ℝ)
      exact_mod_cast this
    exact ((by fun_prop : Continuous (fun t : ℝ => ρ * (t - μ))).intervalIntegrable 0 T).sub
      (hmono.intervalIntegrable)
  -- the three integrands
  set H1 : ℝ → S.Ω → ℝ := fun t ω => GpathT (G1c ρ μ C) μ (fun s => S.N s ω) (fun s => P.U s ω) t
  set H2 : ℝ → S.Ω → ℝ := fun t ω => Gpath G2 μ (fun s => S.N s ω) (fun s => P.U s ω) t
  set G3 : ℕ → ℕ → ℝ → ℝ := fun a v t => clampC C (ρ * (t - μ) - a) with hG3
  have hG3c : ∀ a v, Continuous (G3 a v) := fun a v => (clampC_cont C).comp (by fun_prop)
  set H3 : ℝ → S.Ω → ℝ := fun t ω => GpathT G3 μ (fun s => S.N s ω) (fun s => P.U s ω) t
  set Hl1 : ℕ → S.Ω → ℝ := fun k ω => G1c ρ μ C
    (vS μ (fun s => S.N s ω) (fun s => P.U s ω) (leftLim (fun s => S.N s ω) (arrT (fun s => S.N s ω) k)))
    (vAv μ (fun s => S.N s ω) (fun s => P.U s ω) k) (arrT (fun s => S.N s ω) k)
  set Hl2 : ℕ → S.Ω → ℝ := fun k ω => G2
    (vS μ (fun s => S.N s ω) (fun s => P.U s ω) (leftLim (fun s => S.N s ω) (arrT (fun s => S.N s ω) k)))
    (vAv μ (fun s => S.N s ω) (fun s => P.U s ω) k)
  set Hl3 : ℕ → S.Ω → ℝ := fun k ω => G3
    (vS μ (fun s => S.N s ω) (fun s => P.U s ω) (leftLim (fun s => S.N s ω) (arrT (fun s => S.N s ω) k)))
    (vAv μ (fun s => S.N s ω) (fun s => P.U s ω) k) (arrT (fun s => S.N s ω) k)
  have hG2b : ∀ a v, |G2 a v| ≤ 1 := by intro a v; unfold G2; split_ifs <;> simp
  obtain ⟨hi1a, hi1b, he1⟩ := compensation S T hT H1 (1 + 2 * C)
    (fun t _ => measurable_Gproc S P (fun a v => G1c ρ μ C a v t) μ hμ t)
    (fun t ω => G1c_bdd hC0 ρ μ _ _ t) Hl1
    (fun ω k _ _ => GpathT_left (G1c ρ μ C) (G1c_cont ρ μ C) (P.pathOK S μ hμ ω) _)
    (fun ω => GpathT_left_ae (G1c ρ μ C) (G1c_cont ρ μ C) (P.pathOK S μ hμ ω) T)
  obtain ⟨hi2a, hi2b, he2⟩ := compensation S T hT H2 1
    (fun t _ => measurable_Gproc S P G2 μ hμ t) (fun t ω => hG2b _ _) Hl2
    (fun ω k _ _ => Gpath_left G2 (P.pathOK S μ hμ ω) _)
    (fun ω => Gpath_left_ae G2 (P.pathOK S μ hμ ω) T)
  obtain ⟨-, hi3b, -⟩ := compensation S T hT H3 C
    (fun t _ => measurable_Gproc S P (fun a v => G3 a v t) μ hμ t)
    (fun t ω => abs_clampC_le hC0 _) Hl3
    (fun ω k _ _ => GpathT_left G3 hG3c (P.pathOK S μ hμ ω) _)
    (fun ω => GpathT_left_ae G3 hG3c (P.pathOK S μ hμ ω) T)
  -- identify ∫ H3 with ∫ Z
  have hZ3 : ∀ ω, ∫ t in (0:ℝ)..T, (ρ * (t - μ) - tbA S ρ hρ μ ω t) = ∫ t in (0:ℝ)..T, H3 t ω := by
    intro ω
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le hT.le] at ht
    simp only [H3, GpathT, G3]
    exact (clampC_of_abs (hZb ω t ht.1 ht.2)).symm
  have hiZ : Integrable (fun ω => ∫ t in (0:ℝ)..T, (ρ * (t - μ) - tbA S ρ hρ μ ω t)) S.ν := by
    simp_rw [hZ3]; exact hi3b
  have hAm := measurable_tbA S hρ μ hμ T
  have hiA : Integrable (fun ω => (tbA S ρ hρ μ ω T : ℝ)) S.ν :=
    integrable_of_bdd' S hAm (C := ρ * T + 1) (fun ω => by
      obtain ⟨h1, h2⟩ := tbA_le S hρ μ hμ ω le_rfl hT.le
      rw [abs_of_nonneg (Nat.cast_nonneg _)]; linarith)
  have hiZ2 : Integrable (fun ω => (ρ * (T - μ) - tbA S ρ hρ μ ω T) ^ 2) S.ν :=
    integrable_of_bdd' S ((measurable_const.sub hAm).pow_const 2) (C := C ^ 2) (fun ω => by
      have := hZb ω T hT.le le_rfl
      rw [abs_of_nonneg (sq_nonneg _)]
      nlinarith [abs_nonneg (ρ * (T - μ) - (tbA S ρ hρ μ ω T : ℝ)), sq_abs (ρ * (T - μ) - (tbA S ρ hρ μ ω T : ℝ))])
  refine ⟨hiZ, hiZ2, hiA, ?_⟩
  -- pathwise identities on good paths
  have hgood := ae_noBatch S T hT
  have hpath : ∀ᵐ ω ∂S.ν, (ρ * (T - μ) - tbA S ρ hρ μ ω T) ^ 2 - (ρ * μ) ^ 2 =
      2 * ρ * (∫ t in (0:ℝ)..T, (ρ * (t - μ) - tbA S ρ hρ μ ω t)) +
        ∑ k ∈ Finset.Icc 1 (S.N T ω), Hl1 k ω := by
    filter_upwards [hgood] with ω hω
    have h := P.pathOK S μ hμ ω
    have hCk : ∀ k, 1 ≤ k → k ≤ S.N T ω →
        vS μ (fun s => S.N s ω) (fun s => P.U s ω) (k - 1) <
          vAv μ (fun s => S.N s ω) (fun s => P.U s ω) k →
        |ρ * (arrT (fun s => S.N s ω) k - μ) -
          vS μ (fun s => S.N s ω) (fun s => P.U s ω) (k - 1)| ≤ C := by
      intro k hk1 hkT hlt
      have hσ0 := arrT_pos h.hN h.hN0 hk1 hkT
      have hσT := arrT_le h.hN h.hN0 hk1 hkT
      have hv : (vAv μ (fun s => S.N s ω) (fun s => P.U s ω) k : ℝ) ≤ ρ * T + 1 := by
        unfold vAv
        have h1 : leftLim (fun s => P.U s ω) (arrT (fun s => S.N s ω) k - μ) ≤ P.U (T - μ) ω :=
          le_trans (leftLim_le_self h.hU.1 _) (h.hU.1 (by linarith))
        have h2 := (tbA_le S hρ μ hμ ω (le_refl T) hT.le).2
        have h3 : (P.U (T - μ) ω : ℝ) = tbU ρ (T - μ) := rfl
        have : ((leftLim (fun s => P.U s ω) (arrT (fun s => S.N s ω) k - μ) : ℕ) : ℝ) ≤
            P.U (T - μ) ω := by exact_mod_cast h1
        linarith
      have hlt' : (vS μ (fun s => S.N s ω) (fun s => P.U s ω) (k - 1) : ℝ) <
          vAv μ (fun s => S.N s ω) (fun s => P.U s ω) k := by exact_mod_cast hlt
      have h0 : (0:ℝ) ≤ vS μ (fun s => S.N s ω) (fun s => P.U s ω) (k - 1) := Nat.cast_nonneg _
      rw [abs_le]; constructor <;> nlinarith
    obtain ⟨-, hid⟩ := tb_pathwise ρ C h hT hω hCk
    rw [intervalIntegral.integral_const_mul] at hid
    exact hid
  have hsum2 : ∀ᵐ ω ∂S.ν, (tbA S ρ hρ μ ω T : ℝ) = ∑ k ∈ Finset.Icc 1 (S.N T ω), Hl2 k ω := by
    filter_upwards [hgood] with ω hω
    exact vA_sumG2 (P.pathOK S μ hμ ω) hω
  -- pointwise drift in time
  have hpt : ∀ ω, ∫ t in (0:ℝ)..T, (2 * ρ * (ρ * (t - μ) - tbA S ρ hρ μ ω t) + H1 t ω) ≤
      ∫ t in (0:ℝ)..T, (-(2 * (1 - ρ)) * (ρ * (t - μ) - tbA S ρ hρ μ ω t) + H2 t ω) := by
    intro ω
    have h := P.pathOK S μ hμ ω
    have hiZt : IntervalIntegrable (fun t => ρ * (t - μ) - (tbA S ρ hρ μ ω t : ℝ)) volume 0 T :=
      hZii ω
    have hi1 : IntervalIntegrable (fun t => H1 t ω) volume 0 T :=
      intervalIntegrable_of_bdd (measurable_GpathT_time _ (G1c_cont ρ μ C) h)
        (fun t => G1c_bdd hC0 ρ μ _ _ t) 0 T
    have hi2 : IntervalIntegrable (fun t => H2 t ω) volume 0 T :=
      intervalIntegrable_of_bdd (measurable_Gpath_time _ h) (fun t => hG2b _ _) 0 T
    apply intervalIntegral.integral_mono_on hT.le ((hiZt.const_mul _).add hi1)
      ((hiZt.const_mul _).add hi2)
    intro t ht
    simp only [H1, H2, GpathT, Gpath, G1c, G2]
    have hZt := hZb ω t ht.1 ht.2
    split_ifs with hlt
    · have : clampC C (ρ * (t - μ) - (vA μ (fun s => S.N s ω) (fun s => P.U s ω) t : ℝ)) =
          ρ * (t - μ) - (tbA S ρ hρ μ ω t : ℝ) := clampC_of_abs hZt
      rw [this]; unfold tbA; ring_nf; linarith
    · have hD := tbU_gt ρ (t - μ) hρ
      have hA : (tbA S ρ hρ μ ω t : ℝ) ≥ (P.U (t - μ) ω : ℝ) := by
        push Not at hlt; exact_mod_cast hlt
      have hU : (P.U (t - μ) ω : ℝ) = tbU ρ (t - μ) := rfl
      simp only [zero_mul, add_zero]
      nlinarith
  -- integrate over ω
  have hstep1 := integral_congr_ae hpath
  rw [integral_sub hiZ2 (integrable_const _), integral_const, smul_eq_mul, probReal_univ, one_mul,
    integral_add (hiZ.const_mul _) hi1a, he1, integral_const_mul] at hstep1
  have hsplit1 : ∀ ω, 2 * ρ * (∫ t in (0:ℝ)..T, (ρ * (t - μ) - tbA S ρ hρ μ ω t)) +
      (∫ t in (0:ℝ)..T, H1 t ω) =
      ∫ t in (0:ℝ)..T, (2 * ρ * (ρ * (t - μ) - tbA S ρ hρ μ ω t) + H1 t ω) := by
    intro ω
    have h := P.pathOK S μ hμ ω
    have hi1 : IntervalIntegrable (fun t => H1 t ω) volume 0 T :=
      intervalIntegrable_of_bdd (measurable_GpathT_time _ (G1c_cont ρ μ C) h)
        (fun t => G1c_bdd hC0 ρ μ _ _ t) 0 T
    rw [intervalIntegral.integral_add ((hZii ω).const_mul _) hi1, intervalIntegral.integral_const_mul]
  have hsplit2 : ∀ ω, ∫ t in (0:ℝ)..T, (-(2 * (1 - ρ)) * (ρ * (t - μ) - tbA S ρ hρ μ ω t) + H2 t ω) =
      -(2 * (1 - ρ)) * (∫ t in (0:ℝ)..T, (ρ * (t - μ) - tbA S ρ hρ μ ω t)) +
        ∫ t in (0:ℝ)..T, H2 t ω := by
    intro ω
    have h := P.pathOK S μ hμ ω
    have hi2 : IntervalIntegrable (fun t => H2 t ω) volume 0 T :=
      intervalIntegrable_of_bdd (measurable_Gpath_time _ h) (fun t => hG2b _ _) 0 T
    rw [intervalIntegral.integral_add ((hZii ω).const_mul _) hi2, intervalIntegral.integral_const_mul]
  have hiL : Integrable (fun ω => ∫ t in (0:ℝ)..T,
      (2 * ρ * (ρ * (t - μ) - tbA S ρ hρ μ ω t) + H1 t ω)) S.ν := by
    simp_rw [← hsplit1]; exact (hiZ.const_mul _).add hi1b
  have hiR : Integrable (fun ω => ∫ t in (0:ℝ)..T,
      (-(2 * (1 - ρ)) * (ρ * (t - μ) - tbA S ρ hρ μ ω t) + H2 t ω)) S.ν := by
    simp_rw [hsplit2]; exact (hiZ.const_mul _).add hi2b
  have hL : ∫ ω, (∫ t in (0:ℝ)..T, (2 * ρ * (ρ * (t - μ) - tbA S ρ hρ μ ω t) + H1 t ω)) ∂S.ν =
      2 * ρ * (∫ ω, (∫ t in (0:ℝ)..T, (ρ * (t - μ) - tbA S ρ hρ μ ω t)) ∂S.ν) +
        ∫ ω, (∫ t in (0:ℝ)..T, H1 t ω) ∂S.ν := by
    simp_rw [← hsplit1]; rw [integral_add (hiZ.const_mul _) hi1b, integral_const_mul]
  have hR : ∫ ω, (∫ t in (0:ℝ)..T,
      (-(2 * (1 - ρ)) * (ρ * (t - μ) - tbA S ρ hρ μ ω t) + H2 t ω)) ∂S.ν =
      -(2 * (1 - ρ)) * (∫ ω, (∫ t in (0:ℝ)..T, (ρ * (t - μ) - tbA S ρ hρ μ ω t)) ∂S.ν) +
        ∫ ω, (∫ t in (0:ℝ)..T, H2 t ω) ∂S.ν := by
    simp_rw [hsplit2]; rw [integral_add (hiZ.const_mul _) hi2b, integral_const_mul]
  have hmono := integral_mono hiL hiR (fun ω => hpt ω)
  have hA : ∫ ω, (tbA S ρ hρ μ ω T : ℝ) ∂S.ν = ∫ ω, (∫ t in (0:ℝ)..T, H2 t ω) ∂S.ν := by
    rw [integral_congr_ae hsum2, he2]
  linarith

end tbexp

end LostSalesRQ

namespace LostSalesRQ

open MeasureTheory ProbabilityTheory Filter Set Topology

section tbcost
variable (S : DemandSpace 1)

lemma tbZ_lower {ρ : ℝ} (hρ : 0 < ρ) (μ : ℝ) (hμ : 0 ≤ μ) (ω : S.Ω) {t T : ℝ} (ht : 0 ≤ t)
    (htT : t ≤ T) (hT : 0 ≤ T) :
    -(1 + ρ * μ) ≤ ρ * (t - μ) - (tbA S ρ hρ μ ω t : ℝ) := by
  have h1 := (tbA_le S hρ μ hμ ω htT hT).1
  rcases lt_or_ge (t - μ) 0 with hneg | hpos
  · have : tbU ρ (t - μ) = 0 := by unfold tbU; rw [if_pos hneg]
    rw [this] at h1; push_cast at h1
    have h0 : (0:ℝ) ≤ tbA S ρ hρ μ ω t := Nat.cast_nonneg _
    nlinarith
  · have := tbU_le ρ (t - μ) hρ hpos
    have : (0:ℝ) ≤ ρ * μ := by positivity
    linarith

/-- Real-valued finite-horizon cost bound for the open-loop policy. -/
theorem tb_cost_real {ℓ : ℝ} (hℓ0 : 0 < ℓ) (hℓ1 : ℓ < 1) (μ a : ℝ) (hμ : 0 ≤ μ) (ha : 0 ≤ a)
    {T : ℝ} (hT : 1 ≤ T) {ε : ℝ} (hε : 0 < ε) :
    let ρ := 1 - ℓ
    ∃ hρ : 0 < ρ,
    Integrable (fun ω => ∫ t in (0:ℝ)..T, ((tbU ρ (t - μ) - tbA S ρ hρ μ ω t : ℕ) : ℝ)) S.ν ∧
    Integrable (fun ω => ((S.N T ω - tbA S ρ hρ μ ω T : ℕ) : ℝ)) S.ν ∧
    (∫ ω, (∫ t in (0:ℝ)..T, ((tbU ρ (t - μ) - tbA S ρ hρ μ ω t : ℕ) : ℝ)) ∂S.ν) +
      a * ∫ ω, ((S.N T ω - tbA S ρ hρ μ ω T : ℕ) : ℝ) ∂S.ν ≤
      T * (1 / (2 * ℓ) + a * ℓ + a * ε) +
        ((((1 - ℓ) * μ) ^ 2 + 1) / (2 * ℓ) + (1 - ℓ) * μ ^ 2 / 2 + 1 / (2 * (1 - ℓ))) +
        a * ((1 - ℓ) * μ + ((((1 - ℓ) * μ) ^ 2 + 1) + (2 * ℓ * (1 + (1 - ℓ) * μ) + (1 - ℓ))) /
          (4 * ε)) := by
  intro ρ
  have hρ : 0 < ρ := by simp only [ρ]; linarith
  have hρ1 : ρ < 1 := by simp only [ρ]; linarith
  refine ⟨hρ, ?_⟩
  have hT0 : 0 < T := by linarith
  obtain ⟨hiZ, hiZ2, hiA, hdrift⟩ := tb_drift S hρ hρ1 μ hμ hT0
  set P := tbPolicy S ρ hρ with hP
  -- pathwise facts
  have hAle : ∀ ω t, tbA S ρ hρ μ ω t ≤ tbU ρ (t - μ) := fun ω t =>
    vA_le (P.pathOK S μ hμ ω) t
  have hZii : ∀ ω, IntervalIntegrable (fun t => ρ * (t - μ) - (tbA S ρ hρ μ ω t : ℝ)) volume 0 T := by
    intro ω
    have h := P.pathOK S μ hμ ω
    have hmono : Monotone (fun t => (tbA S ρ hρ μ ω t : ℝ)) := by
      intro a b hab
      have := srec_mono (vAv μ (fun s => S.N s ω) (fun s => P.U s ω)) (h.hN.1 hab)
      show ((vS μ _ _ (S.N a ω) : ℕ) : ℝ) ≤ ((vS μ _ _ (S.N b ω) : ℕ) : ℝ)
      exact_mod_cast this
    exact ((by fun_prop : Continuous (fun t : ℝ => ρ * (t - μ))).intervalIntegrable 0 T).sub
      (hmono.intervalIntegrable)
  obtain ⟨hdetI, hdet⟩ := tb_det_int hρ μ T hμ hT0.le
  have hX : ∀ ω, ∫ t in (0:ℝ)..T, ((tbU ρ (t - μ) - tbA S ρ hρ μ ω t : ℕ) : ℝ) =
      (∫ t in (0:ℝ)..T, (ρ * (t - μ) - tbA S ρ hρ μ ω t)) +
        ∫ t in (0:ℝ)..T, ((tbU ρ (t - μ) : ℝ) - ρ * (t - μ)) := by
    intro ω
    rw [← intervalIntegral.integral_add (hZii ω) hdetI]
    congr 1; funext t
    rw [Nat.cast_sub (hAle ω t)]; ring
  have hiX : Integrable (fun ω => ∫ t in (0:ℝ)..T, ((tbU ρ (t - μ) - tbA S ρ hρ μ ω t : ℕ) : ℝ)) S.ν := by
    simp_rw [hX]; exact hiZ.add (integrable_const _)
  -- lost sales
  have hNA : ∀ ω, ((S.N T ω - tbA S ρ hρ μ ω T : ℕ) : ℝ) = (S.inc 0 T ω : ℝ) - tbA S ρ hρ μ ω T := by
    intro ω
    have h := P.pathOK S μ hμ ω
    have hle : tbA S ρ hρ μ ω T ≤ S.N T ω := by unfold tbA vA vS; exact srec_le _ _
    have hinc : S.inc 0 T ω = S.N T ω := by
      unfold DemandSpace.inc; rw [S.N_nonpos ω 0 le_rfl, Nat.sub_zero]
    rw [Nat.cast_sub hle, hinc]
  have hiInc := S.integrable_inc le_rfl hT0.le (by linarith)
  have hiL : Integrable (fun ω => ((S.N T ω - tbA S ρ hρ μ ω T : ℕ) : ℝ)) S.ν := by
    simp_rw [hNA]; exact hiInc.sub hiA
  refine ⟨hiX, hiL, ?_⟩
  -- expectations
  set IZ := ∫ ω, (∫ t in (0:ℝ)..T, (ρ * (t - μ) - tbA S ρ hρ μ ω t)) ∂S.ν with hIZ
  set Z2 := ∫ ω, (ρ * (T - μ) - tbA S ρ hρ μ ω T) ^ 2 ∂S.ν with hZ2
  set EA := ∫ ω, (tbA S ρ hρ μ ω T : ℝ) ∂S.ν with hEA
  have hEA_le : EA ≤ ρ * T + 1 := by
    have : ∀ ω, (tbA S ρ hρ μ ω T : ℝ) ≤ ρ * T + 1 := fun ω => by
      obtain ⟨h1, h2⟩ := tbA_le S hρ μ hμ ω le_rfl hT0.le; linarith
    calc EA ≤ ∫ ω, (ρ * T + 1) ∂S.ν := integral_mono hiA (integrable_const _) this
      _ = ρ * T + 1 := by simp
  have hZ2_nn : 0 ≤ Z2 := integral_nonneg (fun ω => sq_nonneg _)
  have hIZ_lo : -(1 + ρ * μ) * T ≤ IZ := by
    have : ∀ ω, -(1 + ρ * μ) * T ≤ ∫ t in (0:ℝ)..T, (ρ * (t - μ) - tbA S ρ hρ μ ω t) := by
      intro ω
      have := intervalIntegral.integral_mono_on hT0.le intervalIntegrable_const (hZii ω)
        (fun t ht => tbZ_lower S hρ μ hμ ω ht.1 ht.2 hT0.le)
      rw [intervalIntegral.integral_const, smul_eq_mul, sub_zero] at this
      linarith
    calc -(1 + ρ * μ) * T = ∫ ω, (-(1 + ρ * μ) * T) ∂S.ν := by simp
      _ ≤ IZ := integral_mono (integrable_const _) hiZ this
  -- holding
  have hHold : ∫ ω, (∫ t in (0:ℝ)..T, ((tbU ρ (t - μ) - tbA S ρ hρ μ ω t : ℕ) : ℝ)) ∂S.ν ≤
      T / (2 * ℓ) + ((ρ * μ) ^ 2 + 1) / (2 * ℓ) + ρ * μ ^ 2 / 2 + 1 / (2 * ρ) := by
    simp_rw [hX]
    rw [integral_add hiZ (integrable_const _), integral_const, smul_eq_mul, probReal_univ, one_mul,
      ← hIZ]
    have h2 : 2 * ℓ * IZ ≤ (ρ * μ) ^ 2 + ρ * T + 1 := by
      have : 2 * (1 - ρ) = 2 * ℓ := by simp only [ρ]; ring
      rw [this] at hdrift; linarith
    have h3 : IZ ≤ ((ρ * μ) ^ 2 + 1) / (2 * ℓ) + ρ * T / (2 * ℓ) := by
      rw [← add_div, le_div_iff₀ (by positivity)]; linarith
    have h4 : ρ * T / (2 * ℓ) + T / 2 = T / (2 * ℓ) := by
      field_simp; simp only [ρ]; ring
    linarith
  -- lost
  have hZT : ∫ ω, (ρ * (T - μ) - tbA S ρ hρ μ ω T) ∂S.ν ≤ ε * T + Z2 / (4 * ε * T) := by
    have hiZT : Integrable (fun ω => ρ * (T - μ) - (tbA S ρ hρ μ ω T : ℝ)) S.ν :=
      (integrable_const _).sub hiA
    have hpt : ∀ ω, ρ * (T - μ) - (tbA S ρ hρ μ ω T : ℝ) ≤
        ε * T + (ρ * (T - μ) - tbA S ρ hρ μ ω T) ^ 2 / (4 * ε * T) := by
      intro ω
      set z := ρ * (T - μ) - (tbA S ρ hρ μ ω T : ℝ)
      rw [← sub_le_iff_le_add', le_div_iff₀ (by positivity)]
      nlinarith [sq_nonneg (z - 2 * ε * T)]
    calc ∫ ω, (ρ * (T - μ) - tbA S ρ hρ μ ω T) ∂S.ν
        ≤ ∫ ω, (ε * T + (ρ * (T - μ) - tbA S ρ hρ μ ω T) ^ 2 / (4 * ε * T)) ∂S.ν :=
          integral_mono hiZT ((integrable_const _).add (hiZ2.div_const _)) hpt
      _ = ε * T + Z2 / (4 * ε * T) := by
          rw [integral_add (integrable_const _) (hiZ2.div_const _), integral_const, smul_eq_mul,
            probReal_univ, one_mul, integral_div]
  have hEZT : ∫ ω, (ρ * (T - μ) - tbA S ρ hρ μ ω T) ∂S.ν = ρ * (T - μ) - EA := by
    rw [integral_sub (integrable_const _) hiA, integral_const, smul_eq_mul, probReal_univ, one_mul]
  have hLost : ∫ ω, ((S.N T ω - tbA S ρ hρ μ ω T : ℕ) : ℝ) ∂S.ν = T - EA := by
    simp_rw [hNA]
    rw [integral_sub hiInc hiA, S.integral_inc le_rfl hT0.le (by linarith)]; ring
  have hZ2b : Z2 ≤ ((ρ * μ) ^ 2 + 1) + (2 * ℓ * (1 + ρ * μ) + ρ) * T := by
    have : 2 * (1 - ρ) = 2 * ℓ := by simp only [ρ]; ring
    rw [this] at hdrift
    nlinarith
  have hZ2T : Z2 / (4 * ε * T) ≤ (((ρ * μ) ^ 2 + 1) + (2 * ℓ * (1 + ρ * μ) + ρ)) / (4 * ε) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have hK : 0 ≤ (ρ * μ) ^ 2 + 1 := by positivity
    have hK1 : 0 ≤ 2 * ℓ * (1 + ρ * μ) + ρ := by positivity
    have h1 : Z2 ≤ (((ρ * μ) ^ 2 + 1) + (2 * ℓ * (1 + ρ * μ) + ρ)) * T := by
      have : ((ρ * μ) ^ 2 + 1) ≤ ((ρ * μ) ^ 2 + 1) * T := by nlinarith
      nlinarith
    have h2 := mul_le_mul_of_nonneg_right h1 (show (0:ℝ) ≤ 4 * ε by positivity)
    calc Z2 * (4 * ε) ≤ (((ρ * μ) ^ 2 + 1) + (2 * ℓ * (1 + ρ * μ) + ρ)) * T * (4 * ε) := h2
      _ = _ := by ring
  have hlost_b : T - EA ≤ ℓ * T + ε * T + ρ * μ +
      (((ρ * μ) ^ 2 + 1) + (2 * ℓ * (1 + ρ * μ) + ρ)) / (4 * ε) := by
    have : T - EA = ℓ * T + ρ * μ + (ρ * (T - μ) - EA) := by simp only [ρ]; ring
    rw [this, ← hEZT]; linarith
  rw [hLost]
  have hfin := add_le_add hHold (mul_le_mul_of_nonneg_left hlost_b ha)
  have hR : T / (2 * ℓ) + ((ρ * μ) ^ 2 + 1) / (2 * ℓ) + ρ * μ ^ 2 / 2 + 1 / (2 * ρ) +
      a * (ℓ * T + ε * T + ρ * μ + (((ρ * μ) ^ 2 + 1) + (2 * ℓ * (1 + ρ * μ) + ρ)) / (4 * ε)) =
      T * (1 / (2 * ℓ) + a * ℓ + a * ε) +
        ((((1 - ℓ) * μ) ^ 2 + 1) / (2 * ℓ) + (1 - ℓ) * μ ^ 2 / 2 + 1 / (2 * (1 - ℓ))) +
        a * ((1 - ℓ) * μ + ((((1 - ℓ) * μ) ^ 2 + 1) + (2 * ℓ * (1 + (1 - ℓ) * μ) + (1 - ℓ))) /
          (4 * ε)) := by
    simp only [ρ]; ring
  linarith

end tbcost

end LostSalesRQ

namespace LostSalesRQ

open MeasureTheory ProbabilityTheory Filter Set Topology

theorem tb_avgCost (S : DemandSpace 1) {ℓ : ℝ} (hℓ0 : 0 < ℓ) (hℓ1 : ℓ < 1) (μ a : ℝ)
    (hμ : 0 ≤ μ) (ha : 0 ≤ a) :
    ∃ π : Policy S, π.avgCost μ 1 a 0 ≤ ENNReal.ofReal (1 / (2 * ℓ) + a * ℓ) := by
  have hρ : 0 < 1 - ℓ := by linarith
  set ρ := 1 - ℓ with hρdef
  set π := tbPolicy S ρ hρ with hπ
  refine ⟨π, ?_⟩
  set c := 1 / (2 * ℓ) + a * ℓ with hc
  -- finite-horizon bound in ENNReal
  have hfin : ∀ ε, 0 < ε → ∀ T, 1 ≤ T → (∫⁻ ω, π.horizonCost μ 1 a 0 T ω ∂S.ν) ≤
      ENNReal.ofReal (T * (c + a * ε) +
        ((((1 - ℓ) * μ) ^ 2 + 1) / (2 * ℓ) + (1 - ℓ) * μ ^ 2 / 2 + 1 / (2 * (1 - ℓ))) +
        a * ((1 - ℓ) * μ + ((((1 - ℓ) * μ) ^ 2 + 1) + (2 * ℓ * (1 + (1 - ℓ) * μ) + (1 - ℓ))) /
          (4 * ε))) := by
    intro ε hε T hT
    obtain ⟨hρ', hiX, hiL, hbound⟩ := tb_cost_real S hℓ0 hℓ1 μ a hμ ha hT hε
    have hT0 : 0 ≤ T := by linarith
    -- per-path conversions
    have hhold : ∀ ω, (∫⁻ t in Icc 0 T, (π.onHand μ t ω : ENNReal)) =
        ENNReal.ofReal (∫ t in (0:ℝ)..T, ((tbU ρ (t - μ) - tbA S ρ hρ μ ω t : ℕ) : ℝ)) := by
      intro ω
      have h := π.pathOK S μ hμ ω
      have hm : Measurable (fun t => tbU ρ (t - μ) - tbA S ρ hρ μ ω t) :=
        (h.hU.1.measurable.comp (measurable_id.sub_const μ)).sub
          ((measurable_from_nat (f := vS μ _ _)).comp h.hN.1.measurable)
      rw [← lintegral_Icc_natCast hm hT0 (C := tbU ρ T) (fun t ht => by
        have : tbU ρ (t - μ) - tbA S ρ hρ μ ω t ≤ tbU ρ T :=
          le_trans (Nat.sub_le _ _) (tbU_mono hρ (by linarith [ht.2]))
        exact_mod_cast this)]
      apply setLIntegral_congr_fun measurableSet_Icc
      intro t _
      simp only [onHand_emptyStart S π (tbPolicy_empty S ρ hρ)]
      rfl
    have hlost : ∀ ω, (π.lost μ T ω : ENNReal) =
        ENNReal.ofReal ((S.N T ω - tbA S ρ hρ μ ω T : ℕ) : ℝ) := by
      intro ω
      rw [ENNReal.ofReal_natCast]
      unfold Policy.lost
      rw [served_emptyStart S π (tbPolicy_empty S ρ hρ)]
      rfl
    have hlostm : Measurable (fun ω => (π.lost μ T ω : ENNReal)) := by
      have hAm : Measurable (fun ω => tbA S ρ hρ μ ω T) :=
        (measurable_vA S π μ hμ T).mono (S.𝓕.le T) le_rfl
      have heq : ∀ ω, π.lost μ T ω = S.N T ω - tbA S ρ hρ μ ω T := fun ω => by
        unfold Policy.lost; rw [served_emptyStart S π (tbPolicy_empty S ρ hρ)]; rfl
      simp_rw [heq]
      exact (measurable_of_countable (fun n : ℕ => (n : ENNReal))).comp ((S.measurable_N T).sub hAm)
    have hE : ∫⁻ ω, π.horizonCost μ 1 a 0 T ω ∂S.ν =
        ENNReal.ofReal (∫ ω, (∫ t in (0:ℝ)..T, ((tbU ρ (t - μ) - tbA S ρ hρ μ ω t : ℕ) : ℝ)) ∂S.ν) +
        ENNReal.ofReal a * ENNReal.ofReal (∫ ω, ((S.N T ω - tbA S ρ hρ μ ω T : ℕ) : ℝ) ∂S.ν) := by
      unfold Policy.horizonCost
      simp only [ENNReal.ofReal_one, one_mul, ENNReal.ofReal_zero, zero_mul, add_zero]
      rw [lintegral_add_right _ (hlostm.const_mul _), lintegral_const_mul _ hlostm]
      simp_rw [hhold, hlost]
      rw [ofReal_integral_eq_lintegral_ofReal hiX (Eventually.of_forall (fun ω =>
          intervalIntegral.integral_nonneg hT0 (fun t _ => Nat.cast_nonneg _))),
        ofReal_integral_eq_lintegral_ofReal hiL (Eventually.of_forall (fun ω => Nat.cast_nonneg _))]
    rw [hE, ← ENNReal.ofReal_mul ha, ← ENNReal.ofReal_add
      (integral_nonneg (fun ω => intervalIntegral.integral_nonneg hT0 (fun t _ => Nat.cast_nonneg _)))
      (mul_nonneg ha (integral_nonneg (fun ω => Nat.cast_nonneg _)))]
    exact ENNReal.ofReal_le_ofReal hbound
  -- limsup
  have hε : ∀ ε, 0 < ε → π.avgCost μ 1 a 0 ≤ ENNReal.ofReal (c + (a + 1) * ε) := by
    intro ε hε
    set R := ((((1 - ℓ) * μ) ^ 2 + 1) / (2 * ℓ) + (1 - ℓ) * μ ^ 2 / 2 + 1 / (2 * (1 - ℓ))) +
        a * ((1 - ℓ) * μ + ((((1 - ℓ) * μ) ^ 2 + 1) + (2 * ℓ * (1 + (1 - ℓ) * μ) + (1 - ℓ))) /
          (4 * ε)) with hR
    have hR0 : 0 ≤ R := by
      have : 0 ≤ (1 - ℓ) * μ := by positivity
      positivity
    unfold Policy.avgCost
    refine limsup_le_of_le (by isBoundedDefault) ?_
    filter_upwards [eventually_ge_atTop (max 1 (R / ε))] with T hT
    have hT1 : 1 ≤ T := le_trans (le_max_left _ _) hT
    have hRT : R ≤ ε * T := by
      have := le_trans (le_max_right _ _) hT
      rw [div_le_iff₀ hε] at this; linarith
    rw [ENNReal.div_le_iff_le_mul (Or.inl (by simp; linarith)) (Or.inl ENNReal.ofReal_ne_top),
      ← ENNReal.ofReal_mul (by positivity)]
    refine le_trans (hfin ε hε T hT1) (ENNReal.ofReal_le_ofReal ?_)
    nlinarith
  have hlim : Tendsto (fun n : ℕ => ENNReal.ofReal (c + (a + 1) * (1 / ((n : ℝ) + 1)))) atTop
      (𝓝 (ENNReal.ofReal c)) := by
    apply ENNReal.tendsto_ofReal
    have := ((tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (a + 1)).const_add c
    simpa using this
  exact ge_of_tendsto' hlim (fun n => hε _ (by positivity))

end LostSalesRQ


namespace LostSalesRQ

open MeasureTheory ProbabilityTheory Filter Set Topology Complex

lemma integral_prod_range_infinitePi {E : Type*} [MeasurableSpace E] (μ : Measure E)
    [IsProbabilityMeasure μ] (f : ℕ → E → ℂ) (hf : ∀ i, Measurable (f i)) (n : ℕ) :
    ∫ x, ∏ i ∈ Finset.range n, f i (x i) ∂(Measure.infinitePi (fun _ : ℕ => μ)) =
      ∏ i ∈ Finset.range n, ∫ y, f i y ∂μ := by
  have hind : iIndepFun (fun (j : Fin n) (x : ℕ → E) => x j)
      (Measure.infinitePi (fun _ : ℕ => μ)) :=
    (iIndepFun_infinitePi (P := fun _ : ℕ => μ) (X := fun _ (y : E) => y)
      (fun _ => measurable_id)).precomp Fin.val_injective
  have h := hind.integral_fun_prod_comp (f := fun (j : Fin n) => f (j : ℕ))
    (fun j => (measurable_pi_apply (j : ℕ)).aemeasurable) (fun j => (hf (j : ℕ)).aestronglyMeasurable)
  rw [← Fin.prod_univ_eq_prod_range (fun i => ∫ y, f i y ∂μ) n]
  have h2 : ∀ x : ℕ → E, ∏ i ∈ Finset.range n, f i (x i) = ∏ j : Fin n, f j (x j) :=
    fun x => (Fin.prod_univ_eq_prod_range (fun i => f i (x i)) n).symm
  simp_rw [h2]
  rw [h]
  congr 1; funext j
  rw [← integral_map (measurable_pi_apply _).aemeasurable (hf j).aestronglyMeasurable,
    Measure.infinitePi_map_eval]

/-- The uniform law on (0, 1]. -/
noncomputable def unif : Measure ℝ := volume.restrict (Ioc (0:ℝ) 1)

instance : IsProbabilityMeasure unif := ⟨by simp [unif]⟩

/-- Clamp into (0, 1]. -/
noncomputable def hcl (v : ℝ) : ℝ := if 0 < v ∧ v ≤ 1 then v else 1

lemma measurable_hcl : Measurable hcl := by
  unfold hcl
  exact Measurable.ite (measurableSet_Ioc) measurable_id measurable_const

lemma hcl_pos (v : ℝ) : 0 < hcl v := by unfold hcl; split_ifs with h; exact h.1; norm_num

lemma hcl_le (v : ℝ) : hcl v ≤ 1 := by unfold hcl; split_ifs with h; exact h.2; norm_num

/-- One unit block: a Poisson(1) count and uniform positions. -/
abbrev Block := ℕ × (ℕ → ℝ)

noncomputable def blockMeasure : Measure Block :=
  (poissonMeasure 1).prod (Measure.infinitePi (fun _ : ℕ => unif))

instance : IsProbabilityMeasure blockMeasure := by unfold blockMeasure; infer_instance

lemma measurable_blockSum (ψ : ℝ → ℝ) (hψ : Measurable ψ) :
    Measurable (fun b : Block => ∑ i ∈ Finset.range b.1, ψ (hcl (b.2 i))) := by
  refine measurable_from_prod_countable_right (fun k => ?_)
  show Measurable (fun y : ℕ → ℝ => ∑ i ∈ Finset.range k, ψ (hcl (y i)))
  exact Finset.measurable_sum _ (fun i _ =>
    hψ.comp (measurable_hcl.comp (measurable_pi_apply i)))

theorem block_charFun (ψ : ℝ → ℝ) (hψ : Measurable ψ) :
    ∫ b, cexp (((∑ i ∈ Finset.range b.1, ψ (hcl (b.2 i)) : ℝ) : ℂ) * I) ∂blockMeasure =
      cexp (∫ v in Ioc (0:ℝ) 1, (cexp ((ψ v : ℂ) * I) - 1)) := by
  set c : ℂ := ∫ v, cexp ((ψ (hcl v) : ℂ) * I) ∂unif with hc
  have hm : Measurable (fun b : Block => cexp (((∑ i ∈ Finset.range b.1, ψ (hcl (b.2 i)) : ℝ) : ℂ) * I)) :=
    Complex.measurable_exp.comp ((Complex.measurable_ofReal.comp (measurable_blockSum ψ hψ)).mul_const I)
  have hint : Integrable (fun b : Block => cexp (((∑ i ∈ Finset.range b.1, ψ (hcl (b.2 i)) : ℝ) : ℂ) * I))
      blockMeasure :=
    Integrable.of_bound (C := 1) hm.aestronglyMeasurable (Eventually.of_forall (fun b => by
      rw [Complex.norm_exp_ofReal_mul_I]))
  unfold blockMeasure
  rw [integral_prod _ hint]
  have hinner : ∀ k : ℕ, ∫ V, cexp (((∑ i ∈ Finset.range k, ψ (hcl (V i)) : ℝ) : ℂ) * I)
      ∂(Measure.infinitePi (fun _ : ℕ => unif)) = c ^ k := by
    intro k
    have : ∀ V : ℕ → ℝ, cexp (((∑ i ∈ Finset.range k, ψ (hcl (V i)) : ℝ) : ℂ) * I) =
        ∏ i ∈ Finset.range k, cexp ((ψ (hcl (V i)) : ℂ) * I) := by
      intro V
      rw [← Complex.exp_sum]; congr 1; push_cast; rw [Finset.sum_mul]
    simp_rw [this]
    rw [integral_prod_range_infinitePi unif (fun _ v => cexp ((ψ (hcl v) : ℂ) * I))
      (fun _ => Complex.measurable_exp.comp ((Complex.measurable_ofReal.comp
        (hψ.comp measurable_hcl)).mul_const I)) k]
    simp [hc]
  simp_rw [hinner]
  rw [integral_poissonMeasure]
  have hc1 : c - 1 = ∫ v in Ioc (0:ℝ) 1, (cexp ((ψ v : ℂ) * I) - 1) := by
    have hcont : IntegrableOn (fun v => cexp ((ψ v : ℂ) * I)) (Ioc (0:ℝ) 1) := by
      refine Measure.integrableOn_of_bounded (M := 1) (by simp) ?_ (Eventually.of_forall (fun v => by
        rw [Complex.norm_exp_ofReal_mul_I]))
      exact (Complex.measurable_exp.comp ((Complex.measurable_ofReal.comp hψ).mul_const I)).aestronglyMeasurable
    rw [integral_sub hcont (integrable_const _), setIntegral_const]
    simp only [Real.volume_real_Ioc, sub_zero, max_eq_left zero_le_one, one_smul]
    rw [hc, unif]
    congr 1
    apply setIntegral_congr_fun measurableSet_Ioc
    intro v hv
    simp only [hcl, if_pos (show 0 < v ∧ v ≤ 1 from hv)]
  rw [← hc1]
  calc ∑' n, (Real.exp (-(1:NNReal)) * ((1:NNReal):ℝ) ^ n / (Nat.factorial n)) • c ^ n
      = ∑' n, ((Real.exp (-1) : ℝ) : ℂ) * (c ^ n / (Nat.factorial n)) := by
        congr with n
        simp only [NNReal.coe_one, one_pow, mul_one, Complex.real_smul]
        push_cast; ring
    _ = ((Real.exp (-1) : ℝ) : ℂ) * ∑' n, (c ^ n / (Nat.factorial n)) := tsum_mul_left
    _ = ((Real.exp (-1) : ℝ) : ℂ) * cexp c := by
        rw [(NormedSpace.expSeries_div_hasSum_exp c).tsum_eq, Complex.exp_eq_exp_ℂ]
    _ = cexp (c - 1) := by
        rw [Complex.ofReal_exp, ← Complex.exp_add]; push_cast; ring_nf

end LostSalesRQ

namespace LostSalesRQ

open MeasureTheory ProbabilityTheory Filter Set Topology

/-- Sample space of the constructed Poisson process. -/
abbrev PΩ := ℕ → Block

noncomputable def Pmeas : Measure PΩ := Measure.infinitePi (fun _ : ℕ => blockMeasure)

instance : IsProbabilityMeasure Pmeas := by unfold Pmeas; infer_instance

/-- Arrival time of point i of block n. -/
noncomputable def ppt (ω : PΩ) (n i : ℕ) : ℝ := n + hcl ((ω n).2 i)

/-- Points of block n at or before t. -/
noncomputable def pcnt (ω : PΩ) (n : ℕ) (t : ℝ) : ℕ :=
  ((Finset.range (ω n).1).filter (fun i => ppt ω n i ≤ t)).card

/-- The counting process. -/
noncomputable def Npp (t : ℝ) (ω : PΩ) : ℕ :=
  ∑ n ∈ Finset.range (⌊t⌋₊ + 1), pcnt ω n t

lemma pcnt_eq_zero (ω : PΩ) {n : ℕ} {t : ℝ} (h : t ≤ n) : pcnt ω n t = 0 := by
  unfold pcnt
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro i _
  unfold ppt
  have := hcl_pos ((ω n).2 i)
  linarith

lemma Npp_eq (ω : PΩ) (t : ℝ) {M : ℕ} (hM : ⌊t⌋₊ + 1 ≤ M) :
    Npp t ω = ∑ n ∈ Finset.range M, pcnt ω n t := by
  unfold Npp
  apply Finset.sum_subset (Finset.range_subset_range.mpr hM)
  intro n hn hn'
  apply pcnt_eq_zero
  simp only [Finset.mem_range, not_lt] at hn'
  have h1 : t < ⌊t⌋₊ + 1 := Nat.lt_floor_add_one t
  have h2 : ((⌊t⌋₊ + 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast hn'
  push_cast at h2
  linarith

lemma Npp_nonpos (ω : PΩ) {t : ℝ} (ht : t ≤ 0) : Npp t ω = 0 := by
  unfold Npp
  exact Finset.sum_eq_zero (fun n _ => pcnt_eq_zero ω (le_trans ht (Nat.cast_nonneg n)))

lemma pcnt_mono (ω : PΩ) (n : ℕ) {s t : ℝ} (hst : s ≤ t) : pcnt ω n s ≤ pcnt ω n t := by
  unfold pcnt
  exact Finset.card_le_card (Finset.monotone_filter_right _ (fun i _ hi => le_trans hi hst))

lemma Npp_mono (ω : PΩ) : Monotone (fun t => Npp t ω) := by
  intro s t hst
  simp only
  rw [Npp_eq ω s (M := ⌊t⌋₊ + 1) (by have := Nat.floor_le_floor (R := ℝ) hst; omega),
    Npp_eq ω t le_rfl]
  exact Finset.sum_le_sum (fun n _ => pcnt_mono ω n hst)

lemma card_filter_rcont (p : ℕ → ℝ) (K : ℕ) (t : ℝ) :
    ∃ δ > 0, ∀ s, t ≤ s → s < t + δ →
      ((Finset.range K).filter (fun i => p i ≤ s)).card =
        ((Finset.range K).filter (fun i => p i ≤ t)).card := by
  induction K with
  | zero => exact ⟨1, one_pos, fun s _ _ => by simp⟩
  | succ K ih =>
    obtain ⟨δ, hδ, hc⟩ := ih
    rcases le_or_gt (p K) t with hp | hp
    · refine ⟨δ, hδ, fun s h1 h2 => ?_⟩
      rw [Finset.range_add_one, Finset.filter_insert, Finset.filter_insert,
        if_pos (le_trans hp h1), if_pos hp,
        Finset.card_insert_of_notMem (by simp), Finset.card_insert_of_notMem (by simp), hc s h1 h2]
    · refine ⟨min δ (p K - t), lt_min hδ (by linarith), fun s h1 h2 => ?_⟩
      have h3 : s < p K := by have := min_le_right δ (p K - t); linarith
      rw [Finset.range_add_one, Finset.filter_insert, Finset.filter_insert,
        if_neg (not_le.mpr h3), if_neg (not_le.mpr hp),
        hc s h1 (lt_of_lt_of_le h2 (by linarith [min_le_left δ (p K - t)]))]

lemma sum_rcont (f : ℕ → ℝ → ℕ) (t : ℝ)
    (hf : ∀ n, ∃ δ > 0, ∀ s, t ≤ s → s < t + δ → f n s = f n t) (M : ℕ) :
    ∃ δ > 0, ∀ s, t ≤ s → s < t + δ →
      ∑ n ∈ Finset.range M, f n s = ∑ n ∈ Finset.range M, f n t := by
  induction M with
  | zero => exact ⟨1, one_pos, fun s _ _ => by simp⟩
  | succ M ih =>
    obtain ⟨δ, hδ, hc⟩ := ih
    obtain ⟨δ', hδ', hc'⟩ := hf M
    refine ⟨min δ δ', lt_min hδ hδ', fun s h1 h2 => ?_⟩
    rw [Finset.sum_range_succ, Finset.sum_range_succ,
      hc s h1 (lt_of_lt_of_le h2 (by linarith [min_le_left δ δ'])),
      hc' s h1 (lt_of_lt_of_le h2 (by linarith [min_le_right δ δ']))]

lemma Npp_rcont (ω : PΩ) (t : ℝ) : ∃ δ > 0, ∀ s, t ≤ s → s < t + δ → Npp s ω = Npp t ω := by
  obtain ⟨δ, hδ, hc⟩ := sum_rcont (fun n s => pcnt ω n s) t
    (fun n => card_filter_rcont (fun i => ppt ω n i) (ω n).1 t) (⌊t⌋₊ + 2)
  refine ⟨min δ 1, lt_min hδ one_pos, fun s h1 h2 => ?_⟩
  have hs1 : s < t + 1 := lt_of_lt_of_le h2 (by linarith [min_le_right δ 1])
  have hfl : ⌊s⌋₊ + 1 ≤ ⌊t⌋₊ + 2 := by
    have : ⌊s⌋₊ < ⌊t⌋₊ + 2 := by
      rw [Nat.floor_lt' (by omega)]
      have := Nat.lt_floor_add_one t
      push_cast; linarith
    omega
  rw [Npp_eq ω s hfl, Npp_eq ω t (M := ⌊t⌋₊ + 2) (by omega)]
  exact hc s h1 (lt_of_lt_of_le h2 (by linarith [min_le_left δ 1]))

lemma measurable_pcnt (n : ℕ) (t : ℝ) : Measurable (fun ω : PΩ => pcnt ω n t) := by
  have hb : Measurable (fun b : Block => ((Finset.range b.1).filter
      (fun i => (n : ℝ) + hcl (b.2 i) ≤ t)).card) := by
    refine measurable_from_prod_countable_right (fun k => ?_)
    show Measurable (fun y : ℕ → ℝ => ((Finset.range k).filter
      (fun i => (n : ℝ) + hcl (y i) ≤ t)).card)
    simp_rw [Finset.card_filter]
    refine Finset.measurable_sum _ (fun i _ => ?_)
    refine Measurable.ite ?_ measurable_const measurable_const
    exact measurableSet_le ((measurable_const.add (measurable_hcl.comp (measurable_pi_apply i))))
      measurable_const
  exact hb.comp (measurable_pi_apply n)

lemma measurable_Npp (t : ℝ) : Measurable (Npp t) := by
  unfold Npp
  exact Finset.measurable_sum _ (fun n _ => measurable_pcnt n t)

end LostSalesRQ

namespace LostSalesRQ

open MeasureTheory ProbabilityTheory Filter Set Topology Complex

/-- Step function with value θ j on (u j, u (j+1)]. -/
noncomputable def stepφ (u θ : ℕ → ℝ) (m : ℕ) (x : ℝ) : ℝ :=
  ∑ j ∈ Finset.range m, θ j * (if u j < x ∧ x ≤ u (j + 1) then 1 else 0)

lemma measurable_stepφ (u θ : ℕ → ℝ) (m : ℕ) : Measurable (stepφ u θ m) := by
  unfold stepφ
  refine Finset.measurable_sum _ (fun j _ => measurable_const.mul ?_)
  exact Measurable.ite (measurableSet_Ioc) measurable_const measurable_const

lemma step_unique {u : ℕ → ℝ} (hu : Monotone u) {x : ℝ} {j j' : ℕ}
    (h : u j < x ∧ x ≤ u (j + 1)) (h' : u j' < x ∧ x ≤ u (j' + 1)) : j = j' := by
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
  · have := hu (show j + 1 ≤ j' by omega); linarith [h.2, h'.1]
  · have := hu (show j' + 1 ≤ j by omega); linarith [h'.2, h.1]

lemma exp_stepφ {u : ℕ → ℝ} (hu : Monotone u) (θ : ℕ → ℝ) (m : ℕ) (x : ℝ) :
    cexp ((stepφ u θ m x : ℂ) * I) - 1 = ∑ j ∈ Finset.range m,
      (if u j < x ∧ x ≤ u (j + 1) then cexp ((θ j : ℂ) * I) - 1 else 0) := by
  by_cases hx : ∃ j ∈ Finset.range m, u j < x ∧ x ≤ u (j + 1)
  · obtain ⟨j0, hj0, hc⟩ := hx
    have h1 : stepφ u θ m x = θ j0 := by
      unfold stepφ
      rw [Finset.sum_eq_single j0]
      · rw [if_pos hc, mul_one]
      · intro j _ hne; rw [if_neg (fun h => hne (step_unique hu h hc)), mul_zero]
      · intro h; exact absurd hj0 h
    rw [h1, Finset.sum_eq_single j0]
    · rw [if_pos hc]
    · intro j _ hne; rw [if_neg (fun h => hne (step_unique hu h hc))]
    · intro h; exact absurd hj0 h
  · push Not at hx
    have h1 : stepφ u θ m x = 0 := by
      unfold stepφ
      exact Finset.sum_eq_zero (fun j hj => by
        rw [if_neg (fun h => absurd h.2 (not_le.mpr (hx j hj h.1))), mul_zero])
    rw [h1, Finset.sum_eq_zero (fun j hj => by
      rw [if_neg (fun h => absurd h.2 (not_le.mpr (hx j hj h.1)))])]
    simp

lemma pcnt_sub (ω : PΩ) (n : ℕ) {a b : ℝ} (hab : a ≤ b) :
    ((pcnt ω n b : ℕ) : ℝ) - pcnt ω n a = ∑ i ∈ Finset.range (ω n).1,
      (if a < ppt ω n i ∧ ppt ω n i ≤ b then (1:ℝ) else 0) := by
  unfold pcnt
  rw [Finset.card_filter, Finset.card_filter]
  push_cast
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  by_cases h1 : ppt ω n i ≤ a
  · rw [if_pos h1, if_pos (le_trans h1 hab), if_neg (fun h => absurd h.1 (not_lt.mpr h1))]; ring
  · rw [if_neg h1]
    by_cases h2 : ppt ω n i ≤ b
    · rw [if_pos h2, if_pos ⟨not_le.mp h1, h2⟩]; ring
    · rw [if_neg h2, if_neg (fun h => h2 h.2)]; ring

lemma incr_sum (ω : PΩ) {u : ℕ → ℝ} (hu : Monotone u) (θ : ℕ → ℝ) (m : ℕ) :
    ∑ j ∈ Finset.range m, θ j * ((Npp (u (j + 1)) ω : ℝ) - Npp (u j) ω) =
      ∑ n ∈ Finset.range (⌊u m⌋₊ + 1), ∑ i ∈ Finset.range (ω n).1, stepφ u θ m (ppt ω n i) := by
  have hM : ∀ j ≤ m, ⌊u j⌋₊ + 1 ≤ ⌊u m⌋₊ + 1 := fun j hj =>
    Nat.add_le_add_right (Nat.floor_le_floor (hu hj)) 1
  have hj : ∀ j ∈ Finset.range m, θ j * ((Npp (u (j + 1)) ω : ℝ) - Npp (u j) ω) =
      ∑ n ∈ Finset.range (⌊u m⌋₊ + 1), ∑ i ∈ Finset.range (ω n).1,
        θ j * (if u j < ppt ω n i ∧ ppt ω n i ≤ u (j + 1) then (1:ℝ) else 0) := by
    intro j hjm
    have hjm' := Finset.mem_range.mp hjm
    rw [Npp_eq ω (u (j + 1)) (hM (j + 1) (by omega)), Npp_eq ω (u j) (hM j (by omega))]
    push_cast
    rw [← Finset.sum_sub_distrib, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n _
    rw [pcnt_sub ω n (hu (Nat.le_succ j)), Finset.mul_sum]
  rw [Finset.sum_congr rfl hj, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro n _
  rw [Finset.sum_comm]
  rfl

end LostSalesRQ

namespace LostSalesRQ

open MeasureTheory ProbabilityTheory Filter Set Topology Complex

lemma integral_step_ind {a b M : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hbM : b ≤ M) (c : ℂ) :
    ∫ x in (0:ℝ)..M, (if a < x ∧ x ≤ b then c else 0) = ((b - a : ℝ) : ℂ) * c := by
  have hM : 0 ≤ M := by linarith
  have : (fun x : ℝ => if a < x ∧ x ≤ b then c else 0) = (Ioc a b).indicator (fun _ => c) := by
    funext x; simp only [Set.indicator_apply, Set.mem_Ioc]
  rw [this, intervalIntegral.integral_of_le hM, setIntegral_indicator measurableSet_Ioc,
    show Ioc (0:ℝ) M ∩ Ioc a b = Ioc a b from
      Set.inter_eq_right.mpr (Set.Ioc_subset_Ioc ha hbM),
    setIntegral_const, Real.volume_real_Ioc_of_le hab, Complex.real_smul]

theorem incr_charFun {u : ℕ → ℝ} (hu : Monotone u) (hu0 : 0 ≤ u 0) (θ : ℕ → ℝ) (m : ℕ) :
    ∫ ω, cexp (((∑ j ∈ Finset.range m, θ j * ((Npp (u (j + 1)) ω : ℝ) - Npp (u j) ω) : ℝ) : ℂ) * I)
      ∂Pmeas = cexp (∑ j ∈ Finset.range m,
        ((u (j + 1) - u j : ℝ) : ℂ) * (cexp ((θ j : ℂ) * I) - 1)) := by
  set M := ⌊u m⌋₊ + 1 with hMdef
  set g : ℝ → ℂ := fun x => cexp ((stepφ u θ m x : ℂ) * I) - 1 with hg
  have hgm : Measurable g := (Complex.measurable_exp.comp ((Complex.measurable_ofReal.comp
    (measurable_stepφ u θ m)).mul_const I)).sub_const 1
  have hgb : ∀ x, ‖g x‖ ≤ 2 := fun x => by
    simp only [hg]
    calc ‖cexp ((stepφ u θ m x : ℂ) * I) - 1‖ ≤ ‖cexp ((stepφ u θ m x : ℂ) * I)‖ + ‖(1:ℂ)‖ :=
          norm_sub_le _ _
      _ = 2 := by rw [Complex.norm_exp_ofReal_mul_I, norm_one]; norm_num
  have hgi : ∀ a b, IntervalIntegrable g volume a b := fun a b => by
    rw [intervalIntegrable_iff]
    exact Measure.integrableOn_of_bounded (M := 2) (by simp) hgm.aestronglyMeasurable
      (Eventually.of_forall hgb)
  -- rewrite the integrand as a product over blocks
  set f : ℕ → Block → ℂ := fun n b =>
    cexp (((∑ i ∈ Finset.range b.1, stepφ u θ m (n + hcl (b.2 i)) : ℝ) : ℂ) * I) with hf
  have hfm : ∀ n, Measurable (f n) := fun n =>
    Complex.measurable_exp.comp ((Complex.measurable_ofReal.comp
      (measurable_blockSum (fun v => stepφ u θ m (n + v))
        ((measurable_stepφ u θ m).comp (measurable_const.add measurable_id)))).mul_const I)
  have hpt : ∀ ω : PΩ, cexp (((∑ j ∈ Finset.range m,
      θ j * ((Npp (u (j + 1)) ω : ℝ) - Npp (u j) ω) : ℝ) : ℂ) * I) =
      ∏ n ∈ Finset.range M, f n (ω n) := by
    intro ω
    rw [incr_sum ω hu θ m, Complex.ofReal_sum, Finset.sum_mul, Complex.exp_sum]
    rfl
  simp_rw [hpt]
  unfold Pmeas
  rw [integral_prod_range_infinitePi blockMeasure f hfm M]
  have hblock : ∀ n, ∫ b, f n b ∂blockMeasure =
      cexp (∫ v in Ioc (0:ℝ) 1, (cexp ((stepφ u θ m (n + v) : ℂ) * I) - 1)) := fun n =>
    block_charFun (fun v => stepφ u θ m (n + v))
      ((measurable_stepφ u θ m).comp (measurable_const.add measurable_id))
  simp_rw [hblock]
  rw [← Complex.exp_sum]
  congr 1
  -- sum of block integrals
  have h1 : ∀ n : ℕ, ∫ v in Ioc (0:ℝ) 1, (cexp ((stepφ u θ m (n + v) : ℂ) * I) - 1) =
      ∫ x in (n:ℝ)..((n + 1 : ℕ) : ℝ), g x := by
    intro n
    rw [← intervalIntegral.integral_of_le zero_le_one]
    have := intervalIntegral.integral_comp_add_left g (n : ℝ) (a := 0) (b := 1)
    simp only [hg, add_zero] at this
    rw [this]; push_cast; rfl
  simp_rw [h1]
  rw [intervalIntegral.sum_integral_adjacent_intervals (a := fun k : ℕ => (k : ℝ))
    (fun k _ => hgi _ _)]
  simp only [Nat.cast_zero]
  have h2 : ∀ x, g x = ∑ j ∈ Finset.range m,
      (if u j < x ∧ x ≤ u (j + 1) then cexp ((θ j : ℂ) * I) - 1 else 0) := fun x =>
    exp_stepφ hu θ m x
  simp_rw [h2]
  rw [intervalIntegral.integral_finset_sum (fun j _ => by
    rw [intervalIntegrable_iff]
    refine Measure.integrableOn_of_bounded (M := 2) (by simp) ?_ (Eventually.of_forall (fun x => ?_))
    · exact (Measurable.ite measurableSet_Ioc measurable_const measurable_const).aestronglyMeasurable
    · split_ifs
      · calc ‖cexp ((θ j : ℂ) * I) - 1‖ ≤ ‖cexp ((θ j : ℂ) * I)‖ + ‖(1:ℂ)‖ := norm_sub_le _ _
          _ = 2 := by rw [Complex.norm_exp_ofReal_mul_I, norm_one]; norm_num
      · simp)]
  apply Finset.sum_congr rfl
  intro j hj
  have hjm := Finset.mem_range.mp hj
  have hM : u (j + 1) ≤ (M : ℝ) := by
    have h3 := hu (show j + 1 ≤ m by omega)
    have h4 := Nat.lt_floor_add_one (u m)
    rw [hMdef]; push_cast; linarith
  exact integral_step_ind (le_trans hu0 (hu (Nat.zero_le j))) (hu (Nat.le_succ j)) hM _

end LostSalesRQ

namespace LostSalesRQ

open MeasureTheory ProbabilityTheory Filter Set Topology Complex

theorem single_charFun {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (θ : ℝ) :
    ∫ ω, cexp (((θ * ((Npp b ω : ℝ) - Npp a ω) : ℝ) : ℂ) * I) ∂Pmeas =
      cexp (((b - a : ℝ) : ℂ) * (cexp ((θ : ℂ) * I) - 1)) := by
  have hu : Monotone (fun j : ℕ => if j = 0 then a else b) := by
    intro i j hij
    simp only
    split_ifs <;> first | exact le_rfl | exact hab | omega
  have := incr_charFun hu (by simp [ha]) (fun _ => θ) 1
  simpa using this

lemma Npp_sub_cast (ω : PΩ) {a b : ℝ} (hab : a ≤ b) :
    ((Npp b ω - Npp a ω : ℕ) : ℝ) = (Npp b ω : ℝ) - Npp a ω :=
  Nat.cast_sub (Npp_mono ω hab)

theorem incr_map {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    Pmeas.map (fun ω => ((Npp b ω - Npp a ω : ℕ) : ℝ)) =
      (poissonMeasure (Real.toNNReal (b - a))).map (Nat.cast : ℕ → ℝ) := by
  have hm : Measurable (fun ω => ((Npp b ω - Npp a ω : ℕ) : ℝ)) :=
    (measurable_from_nat (f := fun n : ℕ => (n : ℝ))).comp
      ((measurable_Npp b).sub (measurable_Npp a))
  apply Measure.ext_of_charFun
  funext θ
  rw [charFun_map_cast_poissonMeasure, charFun_apply, integral_map hm.aemeasurable
    (by fun_prop)]
  simp_rw [Real.inner_apply, Npp_sub_cast _ hab]
  have := single_charFun ha hab θ
  rw [Real.coe_toNNReal _ (by linarith), ← this]
  congr 1; funext ω; congr 2; push_cast; ring

theorem incr_law {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (k : ℕ) :
    Pmeas {ω | Npp b ω - Npp a ω = k} = ENNReal.ofReal (poisMass (1 * (b - a)) k) := by
  have hm : Measurable (fun ω => ((Npp b ω - Npp a ω : ℕ) : ℝ)) :=
    (measurable_from_nat (f := fun n : ℕ => (n : ℝ))).comp
      ((measurable_Npp b).sub (measurable_Npp a))
  have hset : {ω | Npp b ω - Npp a ω = k} = (fun ω => ((Npp b ω - Npp a ω : ℕ) : ℝ)) ⁻¹' {(k : ℝ)} := by
    ext ω; simp
  rw [hset, ← Measure.map_apply hm (measurableSet_singleton _), incr_map ha hab,
    Measure.map_apply (measurable_from_nat (f := fun n : ℕ => (n : ℝ))) (measurableSet_singleton _)]
  have : (Nat.cast : ℕ → ℝ) ⁻¹' {(k : ℝ)} = {k} := by ext n; simp
  rw [this, poissonMeasure_singleton]
  unfold poisMass
  rw [Real.coe_toNNReal _ (by linarith), one_mul, neg_sub]

end LostSalesRQ

namespace LostSalesRQ

open MeasureTheory ProbabilityTheory Filter Set Topology Complex

/-- Real increment of the counting process. -/
noncomputable def incrX (u : ℕ → ℝ) (j : ℕ) (ω : PΩ) : ℝ := (Npp (u (j + 1)) ω : ℝ) - Npp (u j) ω

lemma measurable_incrX (u : ℕ → ℝ) (j : ℕ) : Measurable (incrX u j) :=
  ((measurable_from_nat (f := fun n : ℕ => (n : ℝ))).comp (measurable_Npp _)).sub
    ((measurable_from_nat (f := fun n : ℕ => (n : ℝ))).comp (measurable_Npp _))

theorem incr_iIndep {u : ℕ → ℝ} (hu : Monotone u) (hu0 : 0 ≤ u 0) (m : ℕ) :
    iIndepFun (fun (j : Fin m) => incrX u j) Pmeas := by
  rw [iIndepFun_iff_charFun_pi (X := fun (j : Fin m) => incrX u j)
    (fun (j : Fin m) => (measurable_incrX u (j : ℕ)).aemeasurable)]
  intro t
  set θ : ℕ → ℝ := fun j => if h : j < m then t ⟨j, h⟩ else 0 with hθ
  have hθt : ∀ j : Fin m, θ j = t j := fun j => by simp [hθ, j.2]
  have hmv : Measurable (fun ω => (fun (j : Fin m) => incrX u j ω)) :=
    measurable_pi_lambda _ (fun j => measurable_incrX u j)
  have hmv' : Measurable (fun ω => WithLp.toLp 2 (fun (j : Fin m) => incrX u j ω)) :=
    (WithLp.measurable_toLp 2 _).comp hmv
  rw [charFun_apply, integral_map hmv'.aemeasurable (by fun_prop)]
  simp only [PiLp.inner_apply, Real.inner_apply]
  have hsum : ∀ ω, (∑ j : Fin m, incrX u j ω * t j) =
      ∑ j ∈ Finset.range m, θ j * ((Npp (u (j + 1)) ω : ℝ) - Npp (u j) ω) := by
    intro ω
    rw [← Fin.sum_univ_eq_sum_range (fun j => θ j * ((Npp (u (j + 1)) ω : ℝ) - Npp (u j) ω)) m]
    apply Finset.sum_congr rfl
    intro j _
    rw [hθt j]; unfold incrX; ring
  have hL : ∀ ω, cexp (((∑ j : Fin m, incrX u j ω * t j : ℝ) : ℂ) * I) =
      cexp (((∑ j ∈ Finset.range m, θ j * ((Npp (u (j + 1)) ω : ℝ) - Npp (u j) ω) : ℝ) : ℂ) * I) := by
    intro ω; rw [hsum ω]
  simp_rw [hL]
  rw [incr_charFun hu hu0 θ m]
  have hR : ∀ j : Fin m, charFun (Pmeas.map (incrX u j)) (t j) =
      cexp (((u (j + 1) - u j : ℝ) : ℂ) * (cexp ((θ j : ℂ) * I) - 1)) := by
    intro j
    rw [charFun_apply, integral_map (measurable_incrX u j).aemeasurable (by fun_prop)]
    simp only [Real.inner_apply]
    rw [← single_charFun (le_trans hu0 (hu (Nat.zero_le j))) (hu (Nat.le_succ j)) (θ j)]
    congr 1; funext ω; congr 2; unfold incrX; rw [hθt j]
    simp only [Nat.succ_eq_add_one]; push_cast; ring
  simp_rw [hR]
  rw [← Complex.exp_sum]
  congr 1
  exact (Fin.sum_univ_eq_sum_range (fun j => ((u (j + 1) - u j : ℝ) : ℂ) *
    (cexp ((θ j : ℂ) * I) - 1)) m).symm

end LostSalesRQ

namespace LostSalesRQ

open MeasureTheory ProbabilityTheory Filter Set Topology

/-- Natural filtration of the constructed counting process. -/
noncomputable def ppF : Filtration ℝ (inferInstance : MeasurableSpace PΩ) where
  seq s := ⨆ (u : ℝ) (_ : u ≤ s), MeasurableSpace.comap (Npp u) inferInstance
  mono' := fun a b hab => iSup₂_le (fun u hu => le_iSup₂_of_le (f := fun (u : ℝ) (_ : u ≤ b) =>
    MeasurableSpace.comap (Npp u) inferInstance) u (le_trans hu hab) le_rfl)
  le' := fun s => iSup₂_le (fun u _ => (measurable_Npp u).comap_le)

lemma measurable_of_eventually_eq {α : Type*} {m : MeasurableSpace α} {f : ℕ → α → ℕ} {g : α → ℕ}
    (hf : ∀ n, Measurable[m] (f n)) (h : ∀ x, ∀ᶠ n in atTop, f n x = g x) : Measurable[m] g := by
  refine @measurable_to_countable' ℕ α _ _ m _ (fun k => ?_)
  have : g ⁻¹' {k} = ⋃ n0 : ℕ, ⋂ n : ℕ, (f (n0 + n)) ⁻¹' {k} := by
    ext x
    simp only [mem_preimage, mem_singleton_iff, mem_iUnion, mem_iInter]
    constructor
    · intro hx
      obtain ⟨n0, hn0⟩ := eventually_atTop.mp (h x)
      exact ⟨n0, fun n => by rw [hn0 (n0 + n) (by omega), hx]⟩
    · rintro ⟨n0, hn0⟩
      obtain ⟨n1, hn1⟩ := eventually_atTop.mp (h x)
      rw [← hn1 (n0 + n1) (by omega)]; exact hn0 n1
  rw [this]
  exact MeasurableSet.iUnion (fun n0 => MeasurableSet.iInter (fun n =>
    hf (n0 + n) (measurableSet_singleton k)))

/-- Dyadic grid sigma-algebra on [0, s]. -/
noncomputable def gridσ (s : ℝ) (n : ℕ) : MeasurableSpace PΩ :=
  ⨆ (k : ℕ) (_ : k ≤ 2 ^ n), MeasurableSpace.comap (Npp (s * k / 2 ^ n)) inferInstance

lemma measurable_grid {s : ℝ} {n k : ℕ} (hk : k ≤ 2 ^ n) :
    Measurable[gridσ s n] (Npp (s * k / 2 ^ n)) :=
  Measurable.of_comap_le (le_iSup₂_of_le (f := fun (k : ℕ) (_ : k ≤ 2 ^ n) =>
    MeasurableSpace.comap (Npp (s * k / 2 ^ n)) inferInstance) k hk le_rfl)

lemma gridσ_mono (s : ℝ) : Monotone (gridσ s) := by
  refine monotone_nat_of_le_succ (fun n => iSup₂_le (fun k hk => ?_))
  have h1 : s * (k : ℝ) / 2 ^ n = s * ((2 * k : ℕ) : ℝ) / 2 ^ (n + 1) := by
    push_cast; rw [pow_succ]; field_simp
  rw [h1]
  exact (measurable_grid (s := s) (n := n + 1) (k := 2 * k) (by rw [pow_succ]; omega)).comap_le

lemma ppF_le_grid {s : ℝ} (hs : 0 < s) : ppF s ≤ ⨆ n, gridσ s n := by
  refine iSup₂_le (fun u hu => Measurable.comap_le ?_)
  have hmono : ∀ n, gridσ s n ≤ ⨆ n, gridσ s n := fun n => le_iSup (fun n => gridσ s n) n
  rcases le_or_gt u 0 with hu0 | hu0
  · have : Npp u = fun _ => 0 := funext (fun ω => Npp_nonpos ω hu0)
    rw [this]; exact measurable_const
  rcases eq_or_lt_of_le hu with hus | hus
  · rw [hus]
    have := (measurable_grid (s := s) (n := 0) (k := 1) (by simp)).mono (hmono 0) le_rfl
    simpa using this
  -- 0 < u < s: approximate from the right along the grid
  set kn : ℕ → ℕ := fun n => ⌈2 ^ n * u / s⌉₊ with hkn
  have hkle : ∀ n, kn n ≤ 2 ^ n := fun n => by
    simp only [hkn]
    rw [Nat.ceil_le]; push_cast
    rw [div_le_iff₀ hs]; nlinarith [pow_pos (two_pos (α := ℝ)) n]
  have hge : ∀ n, u ≤ s * (kn n : ℝ) / 2 ^ n := fun n => by
    have h1 : 2 ^ n * u / s ≤ kn n := Nat.le_ceil _
    rw [le_div_iff₀ (by positivity)]
    rw [div_le_iff₀ hs] at h1; linarith
  have hlt : ∀ n, s * (kn n : ℝ) / 2 ^ n < u + s / 2 ^ n := fun n => by
    have h1 : (kn n : ℝ) < 2 ^ n * u / s + 1 := Nat.ceil_lt_add_one (by positivity)
    have h2 : s * (kn n : ℝ) < s * (2 ^ n * u / s + 1) := mul_lt_mul_of_pos_left h1 hs
    have h3 : s * (2 ^ n * u / s + 1) = 2 ^ n * u + s := by field_simp
    rw [div_lt_iff₀ (by positivity), add_mul, div_mul_cancel₀ _ (by positivity)]
    linarith
  refine measurable_of_eventually_eq (f := fun n => Npp (s * (kn n : ℝ) / 2 ^ n))
    (fun n => (measurable_grid (hkle n)).mono (hmono n) le_rfl) (fun ω => ?_)
  obtain ⟨δ, hδ, hc⟩ := Npp_rcont ω u
  have hsmall : Tendsto (fun n : ℕ => s / 2 ^ n) atTop (𝓝 0) := by
    have := (tendsto_pow_atTop_nhds_zero_of_lt_one (r := (1/2 : ℝ)) (by norm_num) (by norm_num)).const_mul s
    simp only [mul_zero] at this
    refine this.congr (fun n => ?_)
    rw [one_div, inv_pow, div_eq_mul_inv]
  filter_upwards [(tendsto_order.1 hsmall).2 δ hδ] with n hn
  exact hc _ (hge n) (by linarith [hlt n])

/-- Grid points with the final interval [s, t]. -/
noncomputable def gridU (s t : ℝ) (n : ℕ) (k : ℕ) : ℝ := if k ≤ 2 ^ n then s * k / 2 ^ n else t

lemma gridU_mono {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (n : ℕ) : Monotone (gridU s t n) := by
  intro k k' hkk
  unfold gridU
  have hp : (0:ℝ) < 2 ^ n := by positivity
  split_ifs with h1 h2 h2
  · exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (by exact_mod_cast hkk) hs) hp.le
  · have : s * (k : ℝ) / 2 ^ n ≤ s := by
      rw [div_le_iff₀ hp]
      have : (k : ℝ) ≤ 2 ^ n := by exact_mod_cast h1
      nlinarith
    linarith
  · omega
  · exact le_rfl

lemma grid_indep {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (n : ℕ) :
    Indep (gridσ s n) (MeasurableSpace.comap (fun ω => Npp t ω - Npp s ω) inferInstance) Pmeas := by
  set u := gridU s t n with hu
  have hmono := gridU_mono hs hst n
  have hu0 : 0 ≤ u 0 := by simp [hu, gridU]
  have hII := incr_iIndep hmono hu0 (2 ^ n + 1)
  set S : Finset (Fin (2 ^ n + 1)) := Finset.univ.filter (fun j => (j : ℕ) < 2 ^ n) with hS
  set T : Finset (Fin (2 ^ n + 1)) := {Fin.last (2 ^ n)} with hT
  have hdisj : Disjoint S T := by
    rw [Finset.disjoint_singleton_right, hS, Finset.mem_filter]; simp
  have hIF := hII.indepFun_finset S T hdisj (fun j => measurable_incrX u j)
  rw [IndepFun_iff_Indep] at hIF
  set VS := fun ω (i : S) => incrX u (i : Fin (2 ^ n + 1)) ω with hVS
  set VT := fun ω (i : T) => incrX u (i : Fin (2 ^ n + 1)) ω with hVT
  -- grid ≤ comap VS
  have hgrid : gridσ s n ≤ MeasurableSpace.comap VS inferInstance := by
    refine iSup₂_le (fun k hk => Measurable.comap_le ?_)
    have hinc : ∀ j, j < 2 ^ n → Measurable[MeasurableSpace.comap VS inferInstance] (incrX u j) := by
      intro j hj
      have hmem : (⟨j, by omega⟩ : Fin (2 ^ n + 1)) ∈ S := by
        rw [hS, Finset.mem_filter]; exact ⟨Finset.mem_univ _, hj⟩
      have : incrX u j = fun ω => VS ω ⟨⟨j, by omega⟩, hmem⟩ := rfl
      rw [this]
      exact (measurable_pi_apply _).comp (comap_measurable VS)
    have hsum : ∀ ω, (Npp (s * k / 2 ^ n) ω : ℝ) = ∑ j ∈ Finset.range k, incrX u j ω := by
      intro ω
      unfold incrX
      rw [Finset.sum_range_sub (fun j => (Npp (u j) ω : ℝ)) k]
      have h0 : u 0 = 0 := by simp [hu, gridU]
      have hk' : u k = s * k / 2 ^ n := by simp [hu, gridU, hk]
      rw [hk', h0, Npp_nonpos ω le_rfl]; simp
    have hmR : Measurable[MeasurableSpace.comap VS inferInstance]
        (fun ω => ∑ j ∈ Finset.range k, incrX u j ω) :=
      Finset.measurable_sum _ (fun j hj => hinc j (by
        have := Finset.mem_range.mp hj; omega))
    have : Npp (s * k / 2 ^ n) = fun ω => ⌊∑ j ∈ Finset.range k, incrX u j ω⌋₊ := by
      funext ω; rw [← hsum ω, Nat.floor_natCast]
    rw [this]
    exact Nat.measurable_floor.comp hmR
  -- comap D ≤ comap VT
  have hD : MeasurableSpace.comap (fun ω => Npp t ω - Npp s ω) inferInstance ≤
      MeasurableSpace.comap VT inferInstance := by
    refine Measurable.comap_le ?_
    have hmem : Fin.last (2 ^ n) ∈ T := by rw [hT]; exact Finset.mem_singleton_self _
    have hlast : incrX u (2 ^ n) = fun ω => VT ω ⟨Fin.last (2 ^ n), hmem⟩ := rfl
    have hm : Measurable[MeasurableSpace.comap VT inferInstance] (incrX u (2 ^ n)) := by
      rw [hlast]; exact (measurable_pi_apply _).comp (comap_measurable VT)
    have : (fun ω => Npp t ω - Npp s ω) = fun ω => ⌊incrX u (2 ^ n) ω⌋₊ := by
      funext ω
      have h1 : u (2 ^ n) = s := by simp [hu, gridU]
      have h2 : u (2 ^ n + 1) = t := by simp [hu, gridU]
      unfold incrX; rw [h1, h2, ← Npp_sub_cast ω hst, Nat.floor_natCast]
    rw [this]
    exact Nat.measurable_floor.comp hm
  exact indep_of_indep_of_le_right (indep_of_indep_of_le_left hIF hgrid) hD

theorem pp_indep {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    Indep (MeasurableSpace.comap (fun ω => Npp t ω - Npp s ω) inferInstance) (ppF s) Pmeas := by
  rcases eq_or_lt_of_le hs with h0 | hpos
  · subst h0
    have : ppF 0 = ⊥ := by
      refine le_antisymm (iSup₂_le (fun u hu => ?_)) bot_le
      have : Npp u = fun _ => 0 := funext (fun ω => Npp_nonpos ω hu)
      rw [this]; exact (measurable_const : Measurable[⊥] (fun _ : PΩ => (0:ℕ))).comap_le
    rw [this]; exact indep_bot_right _
  · have h1 : Indep (⨆ n, gridσ s n)
        (MeasurableSpace.comap (fun ω => Npp t ω - Npp s ω) inferInstance) Pmeas :=
      indep_iSup_of_directed_le (fun n => grid_indep hs hst n)
        (fun n => iSup₂_le (fun k _ => (measurable_Npp _).comap_le))
        (Measurable.comap_le ((measurable_Npp t).sub (measurable_Npp s)))
        (gridσ_mono s).directed_le
    exact (indep_of_indep_of_le_left h1 (ppF_le_grid hpos)).symm

end LostSalesRQ

namespace LostSalesRQ

open MeasureTheory ProbabilityTheory Filter Set Topology

/-- A unit-rate Poisson demand environment. -/
noncomputable def ppSpace : DemandSpace 1 where
  Ω := PΩ
  ν := Pmeas
  𝓕 := ppF
  N := Npp
  N_adapted := fun t => Measurable.of_comap_le (le_iSup₂_of_le (f := fun (u : ℝ) (_ : u ≤ t) =>
    MeasurableSpace.comap (Npp u) inferInstance) t le_rfl le_rfl)
  N_nonpos := fun ω t ht => Npp_nonpos ω ht
  N_mono := Npp_mono
  N_rcont := Npp_rcont
  N_law := fun s t hs hst k => incr_law hs hst k
  N_indep := fun s t hs hst => pp_indep hs hst

theorem tightness_bounds' :
    (∀ μ a : ℝ, 0 ≤ μ → 1 / 2 < a → OPTk μ a 0 ≤ ENNReal.ofReal (Real.sqrt (2 * a))) ∧
    (∀ μ a : ℝ, 0 < a → a < μ → ∀ j : ℕ,
      2 * Real.sqrt (a * (1 - a / μ)) - (1 - a / μ) ≤ baseStockCost μ a j) := by
  refine ⟨fun μ a hμ ha => ?_, fun μ a ha haμ j => tb_part2 μ a ha haμ j⟩
  set r := Real.sqrt (2 * a) with hr
  have hr2 : r ^ 2 = 2 * a := Real.sq_sqrt (by linarith)
  have hr1 : 1 < r := by
    rw [hr, show (1:ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
    exact Real.sqrt_lt_sqrt zero_le_one (by linarith)
  have hr0 : 0 < r := by linarith
  set ℓ := 1 / r with hℓ
  have hℓ0 : 0 < ℓ := by positivity
  have hℓ1 : ℓ < 1 := by rw [hℓ, div_lt_one hr0]; exact hr1
  obtain ⟨π, hπ⟩ := tb_avgCost ppSpace hℓ0 hℓ1 μ a hμ (by linarith)
  have hval : 1 / (2 * ℓ) + a * ℓ = r := by
    rw [hℓ]; field_simp; nlinarith [hr2]
  rw [hval] at hπ
  unfold OPTk OPT
  exact le_trans (iInf₂_le ppSpace π) hπ

end LostSalesRQ


namespace LostSalesRQ

open MeasureTheory ProbabilityTheory Filter Set Topology

section bspath
variable (S : DemandSpace 1) {μ : ℝ} (hμ : 0 ≤ μ) {j : ℕ} (hj : 1 ≤ j) {π : Policy S}
  (hπ : IsRQPolicy μ (j - 1) 1 π)
include hπ

lemma bs_U (t : ℝ) (ω : S.Ω) : π.U t ω = π.served μ t ω := by
  rw [hπ.2 ω t]; simp

include hj in
lemma bs_init {t : ℝ} (ht : 0 ≤ t) (ω : S.Ω) : π.init t ω = j := by
  rw [hπ.1 ω t, if_pos ht]; omega

lemma bs_served_eq (t : ℝ) (ω : S.Ω) : π.served μ t ω =
    srec (custAvail μ (fun s => π.init s ω) (fun s => π.U s ω) (fun s => S.N s ω)) (S.N t ω) := by
  unfold Policy.served
  exact servedPath_srec μ _ _ _ (S.regPath ω) (fun s hs => S.N_nonpos ω s hs) t

lemma bs_served_mono (ω : S.Ω) : Monotone (fun t => π.served μ t ω) := by
  intro a b hab
  simp only [bs_served_eq S hπ]
  exact srec_mono _ (S.N_mono ω hab)

lemma bs_served_nonpos {t : ℝ} (ht : t ≤ 0) (ω : S.Ω) : π.served μ t ω = 0 := by
  rw [bs_served_eq S hπ, S.N_nonpos ω t ht]; rfl

lemma bs_served_le_N (t : ℝ) (ω : S.Ω) : π.served μ t ω ≤ S.N t ω := by
  rw [bs_served_eq S hπ]; exact srec_le _ _

include hj in
lemma bs_served_le (t : ℝ) (ω : S.Ω) : π.served μ t ω ≤ j + π.served μ (t - μ) ω := by
  rw [bs_served_eq S hπ t ω]
  set N : ℝ → ℕ := fun s => S.N s ω with hN
  set av := custAvail μ (fun s => π.init s ω) (fun s => π.U s ω) N with hav
  have hNr : RegPath N := S.regPath ω
  have h0 : ∀ s, s ≤ 0 → N s = 0 := fun s hs => S.N_nonpos ω s hs
  have h0' : ∀ s, s < 0 → N s = 0 := fun s hs => h0 s hs.le
  have hinit_le : ∀ s, π.init s ω ≤ j := fun s => by
    rw [hπ.1 ω s]; split_ifs <;> omega
  rcases Nat.eq_zero_or_pos (N t) with hz | hpos
  · simp only [hN] at hz ⊢; rw [hz]; simp [srec]
  · have hmono : ∀ k k', 1 ≤ k → k ≤ k' → k' ≤ N t → av k ≤ av k' := by
      intro k k' hk hkk hk'
      have harr := arrT_mono' hNr h0' hk hkk hk'
      simp only [hav, custAvail]
      exact Nat.add_le_add (leftLim_mono (π.init_mono ω) harr)
        (leftLim_mono (π.U_mono ω) (by linarith))
    have h1 := srec_le_av av (N t) hmono (N t) hpos le_rfl
    have harrT := arrT_le hNr h0 hpos (le_refl (N t))
    have h2 : av (N t) ≤ j + π.served μ (t - μ) ω := by
      simp only [hav, custAvail]
      refine Nat.add_le_add (le_trans (leftLim_le_self (π.init_mono ω) _) (hinit_le _)) ?_
      refine le_trans (leftLim_le_self (π.U_mono ω) _) ?_
      rw [bs_U S hπ]
      exact bs_served_mono S hπ ω (by linarith)
    exact le_trans h1 h2

include hj in
lemma bs_onHand {t : ℝ} (ht : 0 ≤ t) (ω : S.Ω) :
    (π.onHand μ t ω : ℝ) = j + (π.served μ (t - μ) ω : ℝ) - π.served μ t ω := by
  unfold Policy.onHand delivered
  show ((π.init t ω + π.U (t - μ) ω - π.served μ t ω : ℕ) : ℝ) = _
  rw [bs_init S hj hπ ht ω, bs_U S hπ, Nat.cast_sub (bs_served_le S hj hπ t ω)]
  push_cast; ring

include hj hμ in
/-- Pathwise holding sandwich. -/
theorem bs_hold {T : ℝ} (hT : μ ≤ T) (ω : S.Ω) :
    IntervalIntegrable (fun t => (π.onHand μ t ω : ℝ)) volume 0 T ∧
    (j : ℝ) * T - μ * π.served μ T ω ≤ ∫ t in (0:ℝ)..T, (π.onHand μ t ω : ℝ) ∧
    ∫ t in (0:ℝ)..T, (π.onHand μ t ω : ℝ) ≤ (j : ℝ) * T - μ * π.served μ T ω + μ * j := by
  have hT0 : 0 ≤ T := le_trans hμ hT
  set A : ℝ → ℝ := fun t => (π.served μ t ω : ℝ) with hA
  have hAm : Monotone A := fun a b hab => by
    simp only [hA]; exact_mod_cast bs_served_mono S hπ ω hab
  have hAi : ∀ a b, IntervalIntegrable A volume a b := fun a b => hAm.intervalIntegrable
  have hsm : Monotone (fun t => A (t - μ)) := fun x y hxy => hAm (by linarith)
  have hAs : ∀ a b, IntervalIntegrable (fun t => A (t - μ)) volume a b := fun a b =>
    hsm.intervalIntegrable
  have hcongr : ∀ t ∈ uIcc (0:ℝ) T, (π.onHand μ t ω : ℝ) = j + A (t - μ) - A t := by
    intro t ht
    rw [uIcc_of_le hT0] at ht
    exact bs_onHand S hj hπ ht.1 ω
  have hii : IntervalIntegrable (fun t => (π.onHand μ t ω : ℝ)) volume 0 T := by
    refine (((intervalIntegrable_const (c := (j:ℝ))).add (hAs 0 T)).sub (hAi 0 T)).congr ?_
    rw [uIoc_of_le hT0]
    intro t ht
    exact (bs_onHand S hj hπ ht.1.le ω).symm
  have hint : ∫ t in (0:ℝ)..T, (π.onHand μ t ω : ℝ) = (j : ℝ) * T - ∫ t in (T - μ)..T, A t := by
    rw [intervalIntegral.integral_congr hcongr,
      intervalIntegral.integral_sub ((intervalIntegrable_const).add (hAs 0 T)) (hAi 0 T),
      intervalIntegral.integral_add intervalIntegrable_const (hAs 0 T),
      intervalIntegral.integral_const, intervalIntegral.integral_comp_sub_right (fun t => A t) μ]
    have hneg : ∫ t in (0 - μ)..0, A t = 0 := by
      rw [intervalIntegral.integral_congr (g := fun _ => (0:ℝ)) (fun t ht => by
        rw [uIcc_of_le (by linarith)] at ht
        simp only [hA]; rw [bs_served_nonpos S hπ ht.2 ω]; simp)]
      simp
    rw [← intervalIntegral.integral_add_adjacent_intervals (hAi (0 - μ) 0) (hAi 0 (T - μ)), hneg,
      ← intervalIntegral.integral_add_adjacent_intervals (hAi 0 (T - μ)) (hAi (T - μ) T)]
    simp only [smul_eq_mul, sub_zero]; ring
  have hle : ∀ t ∈ Icc (T - μ) T, A T - j ≤ A t ∧ A t ≤ A T := by
    intro t ht
    have h1 := bs_served_le S hj hπ T ω
    have h2 : (π.served μ T ω : ℝ) ≤ j + π.served μ (T - μ) ω := by exact_mod_cast h1
    exact ⟨by linarith [hAm ht.1], hAm ht.2⟩
  have hlo := intervalIntegral.integral_mono_on (by linarith) intervalIntegrable_const (hAi (T - μ) T)
    (fun t ht => (hle t ht).1)
  have hhi := intervalIntegral.integral_mono_on (by linarith) (hAi (T - μ) T) intervalIntegrable_const
    (fun t ht => (hle t ht).2)
  rw [intervalIntegral.integral_const, smul_eq_mul] at hlo hhi
  refine ⟨hii, ?_, ?_⟩
  · rw [hint]; simp only [hA] at hhi ⊢; nlinarith
  · rw [hint]; simp only [hA] at hlo ⊢; nlinarith

end bspath

end LostSalesRQ


namespace LostSalesRQ

open MeasureTheory ProbabilityTheory Filter Set Topology

lemma N_eq_inc (S : DemandSpace 1) (T : ℝ) (ω : S.Ω) : S.inc 0 T ω = S.N T ω := by
  unfold DemandSpace.inc; rw [S.N_nonpos ω 0 le_rfl, Nat.sub_zero]

section bsexp
variable (S : DemandSpace 1) {μ : ℝ} (hμ : 0 ≤ μ) {j : ℕ} (hj : 1 ≤ j) {π : Policy S}
  (hπ : IsRQPolicy μ (j - 1) 1 π)
include hπ

lemma bs_measurable_served (T : ℝ) : Measurable (fun ω => π.served μ T ω) := by
  have : (fun ω => π.served μ T ω) = π.U T := funext (fun ω => (bs_U S hπ T ω).symm)
  rw [this]; exact (π.U_adapted T).mono (S.𝓕.le T) le_rfl

lemma bs_integrable_served {T : ℝ} (hT : 0 ≤ T) :
    Integrable (fun ω => (π.served μ T ω : ℝ)) S.ν := by
  have hiN := S.integrable_inc le_rfl hT (by linarith)
  refine Integrable.mono' hiN ((measurable_from_nat (f := fun n : ℕ => (n : ℝ))).comp
    (bs_measurable_served S hπ T)).aestronglyMeasurable (Eventually.of_forall (fun ω => ?_))
  rw [Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _), N_eq_inc]
  exact_mod_cast bs_served_le_N S hπ T ω

lemma bs_EA {T : ℝ} (hT : 0 ≤ T) :
    (π.expectedServed μ T).toReal = ∫ ω, (π.served μ T ω : ℝ) ∂S.ν := by
  rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall (fun ω => Nat.cast_nonneg _))
    ((bs_integrable_served S hπ hT).aestronglyMeasurable)]
  unfold Policy.expectedServed
  congr 1
  apply lintegral_congr; intro ω; rw [ENNReal.ofReal_natCast]

include hj hμ in
theorem bs_cost_bounds {a T : ℝ} (hT : μ ≤ T) (hT0 : 0 ≤ T) :
    ENNReal.ofReal ((j : ℝ) * T - μ * ∫ ω, (π.served μ T ω : ℝ) ∂S.ν) +
        ENNReal.ofReal a * ENNReal.ofReal (T - ∫ ω, (π.served μ T ω : ℝ) ∂S.ν) ≤
      ∫⁻ ω, π.horizonCost μ 1 a 0 T ω ∂S.ν ∧
    ∫⁻ ω, π.horizonCost μ 1 a 0 T ω ∂S.ν ≤
      ENNReal.ofReal ((j : ℝ) * T - μ * ∫ ω, (π.served μ T ω : ℝ) ∂S.ν + μ * j) +
        ENNReal.ofReal a * ENNReal.ofReal (T - ∫ ω, (π.served μ T ω : ℝ) ∂S.ν) := by
  have hiA := bs_integrable_served S hπ hT0
  have hiN := S.integrable_inc le_rfl hT0 (by linarith)
  have hAm := bs_measurable_served S hπ T
  -- lost sales
  have hlost : ∀ ω, (π.lost μ T ω : ENNReal) =
      ENNReal.ofReal ((S.inc 0 T ω : ℝ) - π.served μ T ω) := by
    intro ω
    unfold Policy.lost
    rw [N_eq_inc, ← Nat.cast_sub (bs_served_le_N S hπ T ω), ENNReal.ofReal_natCast]
  have hlostm : Measurable (fun ω => (π.lost μ T ω : ENNReal)) := by
    unfold Policy.lost
    exact (measurable_of_countable (fun n : ℕ => (n : ENNReal))).comp ((S.measurable_N T).sub hAm)
  have hL : ∫⁻ ω, (π.lost μ T ω : ENNReal) ∂S.ν =
      ENNReal.ofReal (T - ∫ ω, (π.served μ T ω : ℝ) ∂S.ν) := by
    simp_rw [hlost]
    have h : ENNReal.ofReal (∫ ω, ((S.inc 0 T ω : ℝ) - π.served μ T ω) ∂S.ν) =
        ∫⁻ ω, ENNReal.ofReal ((S.inc 0 T ω : ℝ) - π.served μ T ω) ∂S.ν :=
      ofReal_integral_eq_lintegral_ofReal (hiN.sub hiA) (Eventually.of_forall (fun ω => by
        have := bs_served_le_N S hπ T ω
        show (0:ℝ) ≤ (S.inc 0 T ω : ℝ) - π.served μ T ω
        rw [N_eq_inc, sub_nonneg]; exact_mod_cast this))
    rw [← h, integral_sub hiN hiA, S.integral_inc le_rfl hT0 (by linarith)]
    ring_nf
  -- holding, per path
  have hhold : ∀ ω, (∫⁻ t in Icc 0 T, (π.onHand μ t ω : ENNReal)) =
      ENNReal.ofReal (∫ t in (0:ℝ)..T, (π.onHand μ t ω : ℝ)) := by
    intro ω
    have hm : Measurable (fun t => π.onHand μ t ω) := by
      unfold Policy.onHand delivered
      exact ((π.init_mono ω).measurable.add ((π.U_mono ω).measurable.comp
        (measurable_id.sub_const μ))).sub (bs_served_mono S hπ ω).measurable
    refine lintegral_Icc_natCast hm hT0 (C := j + S.N T ω) (fun t ht => ?_)
    have h1 := bs_onHand S hj hπ ht.1 ω
    have h2 : π.served μ (t - μ) ω ≤ S.N T ω :=
      le_trans (bs_served_le_N S hπ _ ω) (S.N_mono ω (by linarith [ht.2]))
    have h3 : (0:ℝ) ≤ π.served μ t ω := Nat.cast_nonneg _
    have h4 : ((π.served μ (t - μ) ω : ℕ) : ℝ) ≤ S.N T ω := by exact_mod_cast h2
    rw [h1]; push_cast; linarith
  have hpath := fun ω => bs_hold S hμ hj hπ hT ω
  have hcost : ∫⁻ ω, π.horizonCost μ 1 a 0 T ω ∂S.ν =
      (∫⁻ ω, ENNReal.ofReal (∫ t in (0:ℝ)..T, (π.onHand μ t ω : ℝ)) ∂S.ν) +
        ENNReal.ofReal a * ENNReal.ofReal (T - ∫ ω, (π.served μ T ω : ℝ) ∂S.ν) := by
    unfold Policy.horizonCost
    simp only [ENNReal.ofReal_one, one_mul, ENNReal.ofReal_zero, zero_mul, add_zero]
    rw [lintegral_add_right _ (hlostm.const_mul _), lintegral_const_mul _ hlostm, hL]
    simp_rw [hhold]
  rw [hcost]
  have hiLo : Integrable (fun ω => (j : ℝ) * T - μ * (π.served μ T ω : ℝ)) S.ν :=
    (integrable_const _).sub (hiA.const_mul μ)
  have hiHi : Integrable (fun ω => (j : ℝ) * T - μ * (π.served μ T ω : ℝ) + μ * j) S.ν :=
    hiLo.add (integrable_const _)
  have hELo : ∫ ω, ((j : ℝ) * T - μ * (π.served μ T ω : ℝ)) ∂S.ν =
      (j : ℝ) * T - μ * ∫ ω, (π.served μ T ω : ℝ) ∂S.ν := by
    rw [integral_sub (integrable_const _) (hiA.const_mul μ), integral_const, smul_eq_mul,
      probReal_univ, one_mul, integral_const_mul]
  have hEHi : ∫ ω, ((j : ℝ) * T - μ * (π.served μ T ω : ℝ) + μ * j) ∂S.ν =
      (j : ℝ) * T - μ * ∫ ω, (π.served μ T ω : ℝ) ∂S.ν + μ * j := by
    rw [integral_add hiLo (integrable_const _), hELo, integral_const, smul_eq_mul,
      probReal_univ, one_mul]
  constructor
  · gcongr
    calc ENNReal.ofReal ((j : ℝ) * T - μ * ∫ ω, (π.served μ T ω : ℝ) ∂S.ν)
        = ENNReal.ofReal (∫ ω, ((j : ℝ) * T - μ * (π.served μ T ω : ℝ)) ∂S.ν) := by rw [hELo]
      _ ≤ ∫⁻ ω, ENNReal.ofReal ((j : ℝ) * T - μ * (π.served μ T ω : ℝ)) ∂S.ν :=
          ofReal_integral_le hiLo
      _ ≤ _ := lintegral_mono (fun ω => ENNReal.ofReal_le_ofReal (hpath ω).2.1)
  · gcongr
    calc (∫⁻ ω, ENNReal.ofReal (∫ t in (0:ℝ)..T, (π.onHand μ t ω : ℝ)) ∂S.ν)
        ≤ ∫⁻ ω, ENNReal.ofReal ((j : ℝ) * T - μ * (π.served μ T ω : ℝ) + μ * j) ∂S.ν :=
          lintegral_mono (fun ω => ENNReal.ofReal_le_ofReal (hpath ω).2.2)
      _ = ENNReal.ofReal (∫ ω, ((j : ℝ) * T - μ * (π.served μ T ω : ℝ) + μ * j) ∂S.ν) := by
          rw [ofReal_integral_eq_lintegral_ofReal hiHi (Eventually.of_forall (fun ω => by
            have h0 : 0 ≤ ∫ t in (0:ℝ)..T, (π.onHand μ t ω : ℝ) :=
              intervalIntegral.integral_nonneg hT0 (fun t _ => Nat.cast_nonneg _)
            exact le_trans h0 (hpath ω).2.2))]
      _ = _ := by rw [hEHi]

end bsexp

end LostSalesRQ


namespace LostSalesRQ

open MeasureTheory ProbabilityTheory Filter Set Topology

lemma srec_zero_av (n : ℕ) : srec (fun _ => 0) n = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [srec, ih]

theorem noOrder_avgCost (S : DemandSpace 1) (μ a : ℝ) (hμ : 0 ≤ μ) (ha : 0 ≤ a) :
    (noOrderPolicy S).avgCost μ 1 a 0 = ENNReal.ofReal a := by
  set P := noOrderPolicy S with hP
  have hserved : ∀ t ω, P.served μ t ω = 0 := by
    intro t ω
    rw [served_emptyStart S P (fun _ _ => rfl)]
    unfold vA vS
    have : vAv μ (fun s => S.N s ω) (fun s => P.U s ω) = fun _ => 0 := by
      funext k; unfold vAv
      exact le_antisymm (le_trans (leftLim_le_self monotone_const _) (le_refl 0)) (Nat.zero_le _)
    rw [this, srec_zero_av]
  have hcost : ∀ T, 0 ≤ T → ∫⁻ ω, P.horizonCost μ 1 a 0 T ω ∂S.ν =
      ENNReal.ofReal a * ENNReal.ofReal T := by
    intro T hT
    have hon : ∀ t ω, P.onHand μ t ω = 0 := fun t ω => by
      unfold Policy.onHand delivered; rw [hserved]; rfl
    have hlo : ∀ ω, P.lost μ T ω = S.N T ω := fun ω => by
      unfold Policy.lost; rw [hserved]; rfl
    unfold Policy.horizonCost
    simp only [hon, hlo, Nat.cast_zero, lintegral_zero, mul_zero, zero_add, ENNReal.ofReal_zero,
      zero_mul, add_zero]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_N S T hT]
  unfold Policy.avgCost
  apply Tendsto.limsup_eq
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with T hT
  rw [hcost T hT.le, ENNReal.mul_div_cancel_right (by simpa using hT) ENNReal.ofReal_ne_top]

section bslim
variable (S : DemandSpace 1) {μ : ℝ} (hμ : 0 ≤ μ) {j : ℕ} (hj : 1 ≤ j) {π : Policy S}
  (hπ : IsRQPolicy μ (j - 1) 1 π)

include hμ hj hπ in
theorem bs_avgCost {a : ℝ} (ha : 0 ≤ a) :
    π.avgCost μ 1 a 0 = ENNReal.ofReal (baseStockCost μ a j) := by
  set e := lossFraction μ j with he
  set EA : ℝ → ℝ := fun T => ∫ ω, (π.served μ T ω : ℝ) ∂S.ν with hEA
  have hx : Tendsto (fun T => EA T / T) atTop (𝓝 (1 - e)) := by
    refine (base_stock_served_rate μ hμ S j hj π hπ).congr' ?_
    filter_upwards [eventually_ge_atTop 0] with T hT
    rw [bs_EA S hπ hT]
  have hl : Tendsto (fun T => ((j : ℝ) * T - μ * EA T) / T) atTop (𝓝 ((j : ℝ) - μ * (1 - e))) := by
    refine ((tendsto_const_nhds (x := (j:ℝ))).sub (hx.const_mul μ)).congr' ?_
    filter_upwards [eventually_gt_atTop 0] with T hT
    field_simp
  have hu : Tendsto (fun T => ((j : ℝ) * T - μ * EA T + μ * j) / T) atTop
      (𝓝 ((j : ℝ) - μ * (1 - e))) := by
    have h0 : Tendsto (fun T : ℝ => μ * j / T) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_id
    have := ((tendsto_const_nhds (x := (j:ℝ))).sub (hx.const_mul μ)).add h0
    rw [add_zero] at this
    refine this.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with T hT
    field_simp
  have hr : Tendsto (fun T => (T - EA T) / T) atTop (𝓝 e) := by
    have := (tendsto_const_nhds (x := (1:ℝ))).sub hx
    rw [sub_sub_cancel] at this
    refine this.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with T hT
    field_simp
  set Lim := ENNReal.ofReal ((j : ℝ) - μ * (1 - e)) + ENNReal.ofReal a * ENNReal.ofReal e with hLim
  have hlow : Tendsto (fun T => ENNReal.ofReal (((j : ℝ) * T - μ * EA T) / T) +
      ENNReal.ofReal a * ENNReal.ofReal ((T - EA T) / T)) atTop (𝓝 Lim) :=
    (ENNReal.tendsto_ofReal hl).add (ENNReal.Tendsto.const_mul (ENNReal.tendsto_ofReal hr)
      (Or.inr ENNReal.ofReal_ne_top))
  have hup : Tendsto (fun T => ENNReal.ofReal (((j : ℝ) * T - μ * EA T + μ * j) / T) +
      ENNReal.ofReal a * ENNReal.ofReal ((T - EA T) / T)) atTop (𝓝 Lim) :=
    (ENNReal.tendsto_ofReal hu).add (ENNReal.Tendsto.const_mul (ENNReal.tendsto_ofReal hr)
      (Or.inr ENNReal.ofReal_ne_top))
  have hsq : Tendsto (fun T => (∫⁻ ω, π.horizonCost μ 1 a 0 T ω ∂S.ν) / ENNReal.ofReal T) atTop
      (𝓝 Lim) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow hup ?_ ?_
    · filter_upwards [eventually_ge_atTop (max μ 1)] with T hT
      have hT1 : μ ≤ T := le_trans (le_max_left _ _) hT
      have hTp : 0 < T := lt_of_lt_of_le one_pos (le_trans (le_max_right _ _) hT)
      have hb := (bs_cost_bounds S hμ hj hπ (a := a) hT1 hTp.le).1
      have := ENNReal.div_le_div_right hb (ENNReal.ofReal T)
      rw [ENNReal.add_div, mul_div_assoc, ← ENNReal.ofReal_div_of_pos hTp,
        ← ENNReal.ofReal_div_of_pos hTp] at this
      exact this
    · filter_upwards [eventually_ge_atTop (max μ 1)] with T hT
      have hT1 : μ ≤ T := le_trans (le_max_left _ _) hT
      have hTp : 0 < T := lt_of_lt_of_le one_pos (le_trans (le_max_right _ _) hT)
      have hb := (bs_cost_bounds S hμ hj hπ (a := a) hT1 hTp.le).2
      have := ENNReal.div_le_div_right hb (ENNReal.ofReal T)
      rw [ENNReal.add_div, mul_div_assoc, ← ENNReal.ofReal_div_of_pos hTp,
        ← ENNReal.ofReal_div_of_pos hTp] at this
      exact this
  unfold Policy.avgCost
  rw [hsq.limsup_eq, hLim]
  have he0 : 0 ≤ e := by
    rw [he]; unfold lossFraction poisMass poisCdf
    apply div_nonneg (div_nonneg (mul_nonneg (Real.exp_pos _).le (pow_nonneg hμ _)) (Nat.cast_nonneg _))
    exact Finset.sum_nonneg (fun i _ =>
      div_nonneg (mul_nonneg (Real.exp_pos _).le (pow_nonneg hμ _)) (Nat.cast_nonneg _))
  have hH0 : 0 ≤ (j : ℝ) - μ * (1 - e) := by
    rcases eq_or_lt_of_le hμ with h0 | hpos
    · rw [← h0]; simp
    · have := TBE.moh_nonneg hpos j
      unfold meanOnHand at this; rw [he]; linarith
  rw [← ENNReal.ofReal_mul ha, ← ENNReal.ofReal_add hH0 (mul_nonneg ha he0)]
  unfold baseStockCost meanOnHand
  congr 1; rw [he]; ring

end bslim

theorem exact_base_stock_cost' (μ a : ℝ) (hμ : 0 ≤ μ) (ha : 0 ≤ a) (S : DemandSpace 1) :
    (noOrderPolicy S).avgCost μ 1 a 0 = ENNReal.ofReal a ∧
    ∀ j : ℕ, 1 ≤ j → ∀ π : Policy S, IsRQPolicy μ (j - 1) 1 π →
      π.avgCost μ 1 a 0 = ENNReal.ofReal (baseStockCost μ a j) :=
  ⟨noOrder_avgCost S μ a hμ ha, fun j hj π hπ => bs_avgCost S hμ hj hπ ha⟩

end LostSalesRQ

open LostSalesRQ in
theorem solution (μ a : ℝ) (hμ : 0 ≤ μ) (ha : 0 ≤ a) (S : DemandSpace 1) :
    (noOrderPolicy S).avgCost μ 1 a 0 = ENNReal.ofReal a ∧
    ∀ j : ℕ, 1 ≤ j → ∀ π : Policy S, IsRQPolicy μ (j - 1) 1 π →
      π.avgCost μ 1 a 0 = ENNReal.ofReal (baseStockCost μ a j) :=
  exact_base_stock_cost' μ a hμ ha S
