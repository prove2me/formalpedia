-- Prove2me | solution 1 for LostSalesRQ.brownian_comparison
-- status  : ACCEPTED   (prove)
-- author  : @Ming Hu
-- created : 2026-11-17T23:50:43.527605+00:00
-- url     : https://prove2.me/submissions/27d65191-44a9-4a57-aa8f-5ac28bfd2009

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
import Definitions.Def_LostSalesRQ_gaussian
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.Gamma
import Mathlib.Analysis.Real.Pi.Bounds

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

lemma pc_pos' (t : ℝ) (ht : 0 ≤ t) (n : ℕ) : 0 < poisCdf t n := by
  have h0 : 0 < poisMass t 0 := by unfold poisMass; simp [Real.exp_pos]
  unfold poisCdf
  calc (0:ℝ) < poisMass t 0 := h0
    _ ≤ ∑ i ∈ Finset.range (n + 1), poisMass t i :=
      Finset.single_le_sum (fun i _ => d2_pm_nonneg t ht i)
        (Finset.mem_range.mpr (Nat.succ_pos n))

lemma sum_i_pm_le (t : ℝ) (ht : 0 ≤ t) (n : ℕ) :
    ∑ i ∈ Finset.range (n + 1), (i : ℝ) * poisMass t i ≤ n * poisCdf t n := by
  unfold poisCdf
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  have : (i : ℝ) ≤ n := by exact_mod_cast Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  exact mul_le_mul_of_nonneg_right this (d2_pm_nonneg t ht i)

lemma pm_cross (t : ℝ) (ht : 0 ≤ t) (n : ℕ) :
    poisMass t (n + 1) * poisCdf t n ≤ poisMass t n * poisCdf t (n + 1) := by
  have hs := sum_i_pm t (n + 1)
  have hle := sum_i_pm_le t ht (n + 1)
  have hF := pc_succ t n
  have hp := pm_succ t n
  have hpn := d2_pm_nonneg t ht n
  have h0 : t * poisCdf t n = ∑ i ∈ Finset.range (n + 1 + 1), (i : ℝ) * poisMass t i := by
    rw [hs, hF]; ring
  have h1 : t * poisCdf t n ≤ ((n:ℝ) + 1) * poisCdf t (n + 1) := by
    rw [h0]; push_cast at hle; exact hle
  have h2 : ((n:ℝ) + 1) * (poisMass t n * poisCdf t (n + 1) - poisMass t (n + 1) * poisCdf t n) =
      poisMass t n * (((n:ℝ) + 1) * poisCdf t (n + 1) - t * poisCdf t n) := by
    linear_combination (-(poisCdf t n)) * hp
  have h3 : 0 ≤ poisMass t n * (((n:ℝ) + 1) * poisCdf t (n + 1) - t * poisCdf t n) :=
    mul_nonneg hpn (by linarith)
  have hn1 : (0:ℝ) < (n:ℝ) + 1 := by positivity
  nlinarith

lemma wfun_down (η t : ℝ) (hη : 0 ≤ η) (ht : 0 ≤ t) (n : ℕ) (h : 0 < wfun η (n + 1) t) :
    0 < wfun η n t := by
  unfold wfun at h ⊢
  have hc := pm_cross t ht n
  have hF1 := pc_pos' t ht (n + 1)
  have hF0 := pc_pos' t ht n
  have h1 : η * (poisMass t (n + 1) * poisCdf t n) ≤ η * (poisMass t n * poisCdf t (n + 1)) :=
    mul_le_mul_of_nonneg_left hc hη
  have h2 : poisCdf t (n + 1) * poisCdf t n < η * poisMass t (n + 1) * poisCdf t n :=
    mul_lt_mul_of_pos_right (by linarith) hF0
  have h3 : poisCdf t n * poisCdf t (n + 1) < (η * poisMass t n) * poisCdf t (n + 1) := by
    nlinarith
  have := lt_of_mul_lt_mul_right h3 hF1.le
  linarith

lemma partial_sum_le_peak (a : ℕ → ℝ) (m₀ : ℕ) (hpos : ∀ i < m₀, 0 ≤ a i)
    (hneg : ∀ i, m₀ ≤ i → a i ≤ 0) (m : ℕ) :
    ∑ i ∈ Finset.range m, a i ≤ ∑ i ∈ Finset.range m₀, a i := by
  rcases le_total m m₀ with h | h
  · rw [← Finset.sum_range_add_sum_Ico _ h]
    have : 0 ≤ ∑ i ∈ Finset.Ico m m₀, a i :=
      Finset.sum_nonneg (fun i hi => hpos i (Finset.mem_Ico.mp hi).2)
    linarith
  · rw [← Finset.sum_range_add_sum_Ico _ h]
    have : ∑ i ∈ Finset.Ico m₀ m, a i ≤ 0 :=
      Finset.sum_nonpos (fun i hi => hneg i (Finset.mem_Ico.mp hi).1)
    linarith

lemma calib_analytic (μ η : ℝ) (hμ : 0 ≤ μ) (hη : 1 ≤ η) :
    rankBound μ η + agingRateSup μ η =
      η + ∑ n ∈ Finset.range ⌈(1 - 1 / η) * μ⌉₊,
        (wfun η n (n / (1 - 1 / η)) - wfun η n μ) := by
  have hη0 : 0 < η := by linarith
  have hfη : η * (1 - 1 / η) = η - 1 := by field_simp
  set d : ℕ → ℝ := fun n => wfun η n μ with hd
  set c : ℕ → ℝ := fun n => wfun η n (tauStar η μ n) with hc
  have hex : ∃ n, d n ≤ 0 := by
    refine ⟨⌊η * μ⌋₊ + 1, ?_⟩
    have := aging_term_le η μ μ hη0.le hμ le_rfl (⌊η * μ⌋₊ + 1)
    have hnot : ¬ (((⌊η * μ⌋₊ + 1 : ℕ) : ℝ) ≤ η * μ) := by
      push_cast; push Not; exact Nat.lt_floor_add_one (η * μ)
    rw [if_neg hnot] at this
    exact this
  classical
  set m₀ := Nat.find hex with hm₀
  have hlt : ∀ n < m₀, 0 < d n := fun n hn => by
    have := Nat.find_min hex hn
    push Not at this; exact this
  have hdown : ∀ j k, 0 < d (j + k) → 0 < d j := by
    intro j k
    induction k with
    | zero => simp
    | succ k ih => intro h; exact ih (wfun_down η μ hη0.le hμ (j + k) h)
  have hge : ∀ n, m₀ ≤ n → d n ≤ 0 := by
    intro n hn
    by_contra hpos; push Not at hpos
    have h1 : 0 < d (m₀ + (n - m₀)) := by rw [Nat.add_sub_cancel' hn]; exact hpos
    have h2 := hdown m₀ (n - m₀) h1
    exact absurd (Nat.find_spec hex) (not_le.mpr h2)
  have hF2 : ∀ n : ℕ, (n : ℝ) < (1 - 1 / η) * μ → 0 < d n := by
    intro n hn
    have hμpos : 0 < μ := by
      rcases hμ.eq_or_lt with h0 | h0
      · rw [← h0, mul_zero] at hn; exact absurd hn (not_lt.mpr (Nat.cast_nonneg n))
      · exact h0
    have hs := sum_i_pm μ n
    have hle := sum_i_pm_le μ hμ n
    have hF := pc_pos' μ hμ n
    have hn' : η * n < (η - 1) * μ := by
      have := mul_lt_mul_of_pos_left hn hη0
      rw [← mul_assoc, hfη] at this; exact this
    have h1 : μ * (poisCdf μ n - poisMass μ n) ≤ n * poisCdf μ n := by rw [← hs]; exact hle
    have h4 : η * (μ * (poisCdf μ n - poisMass μ n)) ≤ η * (n * poisCdf μ n) :=
      mul_le_mul_of_nonneg_left h1 hη0.le
    have h5 : 0 < poisCdf μ n * ((η - 1) * μ - η * n) := mul_pos hF (by linarith)
    have h6 : 0 < μ * (η * poisMass μ n - poisCdf μ n) := by nlinarith
    show 0 < η * poisMass μ n - poisCdf μ n
    by_contra hX; push Not at hX
    have := mul_nonpos_of_nonneg_of_nonpos hμ hX
    linarith
  set K := ⌈(1 - 1 / η) * μ⌉₊ with hK
  have hKm : K ≤ m₀ := by
    by_contra h; push Not at h
    have : (m₀ : ℝ) < (1 - 1 / η) * μ := Nat.lt_ceil.mp h
    exact absurd (Nat.find_spec hex) (not_le.mpr (hF2 m₀ this))
  have hcd : ∀ n, d n ≤ c n := fun n => wfun_le_tauStar η μ hη hμ n μ hμ le_rfl
  have hceq : ∀ n, K ≤ n → c n = d n := by
    intro n hn
    have : ¬ ((n : ℝ) < (1 - 1 / η) * μ) := by push Not; exact Nat.ceil_le.mp hn
    simp only [hc, hd, tauStar, if_neg this]
  have hcK : ∀ n < K, c n = wfun η n (n / (1 - 1 / η)) := by
    intro n hn
    have : (n : ℝ) < (1 - 1 / η) * μ := Nat.lt_ceil.mp hn
    simp only [hc, tauStar, if_pos this]
  have hV : ∀ l, expectedShortfall μ l + η * poisTail μ l = η - ∑ n ∈ Finset.range l, d n := by
    intro l; rw [rank_V]; rfl
  have hB : rankBound μ η = η - ∑ n ∈ Finset.range m₀, d n := by
    unfold rankBound
    simp only [hV]
    apply le_antisymm
    · refine ciInf_le ⟨η - ∑ n ∈ Finset.range m₀, d n, ?_⟩ m₀
      rintro _ ⟨l, rfl⟩
      linarith [partial_sum_le_peak d m₀ (fun i hi => (hlt i hi).le) hge l]
    · apply le_ciInf; intro l
      linarith [partial_sum_le_peak d m₀ (fun i hi => (hlt i hi).le) hge l]
  have hD : agingRateSup μ η = ∑ n ∈ Finset.range m₀, c n := by
    unfold agingRateSup
    apply IsGreatest.csSup_eq
    constructor
    · refine ⟨m₀, fun i => tauStar η μ i, fun i j hij => tauStar_mono η μ hη hμ hij,
        fun i => tauStar_mem η μ hη hμ i, ?_⟩
      exact (Fin.sum_univ_eq_sum_range c m₀).symm
    · rintro x ⟨m, τ, hm, hτ, rfl⟩
      calc ∑ i : Fin m, (η * poisMass (τ i) (i : ℕ) - poisCdf (τ i) (i : ℕ))
          ≤ ∑ i : Fin m, c i :=
            Finset.sum_le_sum (fun i _ => wfun_le_tauStar η μ hη hμ i (τ i) (hτ i).1 (hτ i).2)
        _ = ∑ n ∈ Finset.range m, c n := Fin.sum_univ_eq_sum_range c m
        _ ≤ ∑ n ∈ Finset.range m₀, c n :=
            partial_sum_le_peak c m₀ (fun i hi => (hlt i hi).le.trans (hcd i))
              (fun i hi => by rw [hceq i (hKm.trans hi)]; exact hge i hi) m
  rw [hB, hD]
  have hsplit : ∑ n ∈ Finset.range m₀, c n - ∑ n ∈ Finset.range m₀, d n =
      ∑ n ∈ Finset.range K, (wfun η n (n / (1 - 1 / η)) - wfun η n μ) := by
    rw [← Finset.sum_sub_distrib, ← Finset.sum_range_add_sum_Ico _ hKm]
    have h1 : ∑ n ∈ Finset.Ico K m₀, (c n - d n) = 0 :=
      Finset.sum_eq_zero (fun n hn => by rw [hceq n (Finset.mem_Ico.mp hn).1]; ring)
    rw [h1, add_zero]
    apply Finset.sum_congr rfl
    intro n hn
    rw [hcK n (Finset.mem_range.mp hn)]
  linarith [hsplit]

end LostSalesRQ

namespace LostSalesRQ

open MeasureTheory ProbabilityTheory Filter Set Topology

/-- The level x is first exceeded (just before an arrival) at arrival index n. -/
def firstPass (f x : ℝ) (n : ℕ) : Set DemandPath :=
  {ξ | (∀ k < n, f * arrivalEpoch ξ k - k ≤ x) ∧ x < f * arrivalEpoch ξ n - n}

lemma measurableSet_firstPass (f x : ℝ) (n : ℕ) : MeasurableSet (firstPass f x n) := by
  have : firstPass f x n = (⋂ k ∈ Finset.range n, {ξ | f * arrivalEpoch ξ k - k ≤ x}) ∩
      {ξ | x < f * arrivalEpoch ξ n - n} := by
    ext ξ; simp [firstPass]
  rw [this]
  refine MeasurableSet.inter (Finset.measurableSet_biInter _ (fun k _ => ?_)) ?_
  · exact measurableSet_le (((measurable_arrivalEpoch k).const_mul f).sub_const _) measurable_const
  · exact measurableSet_lt measurable_const (((measurable_arrivalEpoch n).const_mul f).sub_const _)

lemma firstPass_cons (f x a : ℝ) (n : ℕ) :
    {ξ : DemandPath | consPath (a, ξ) ∈ firstPass f x (n + 1)} =
      if f * a ≤ x then firstPass f (x + 1 - f * a) n else ∅ := by
  ext ξ
  split_ifs with h
  · simp only [firstPass, mem_ofPred_eq]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨fun k hk => ?_, ?_⟩
      · have := h1 (k + 1) (by omega)
        rw [arrivalEpoch_cons_succ] at this; push_cast at this; linarith
      · rw [arrivalEpoch_cons_succ] at h2; push_cast at h2; linarith
    · rintro ⟨h1, h2⟩
      refine ⟨fun k hk => ?_, ?_⟩
      · cases k with
        | zero => simpa [arrivalEpoch_cons_zero] using h
        | succ k =>
          have := h1 k (by omega)
          rw [arrivalEpoch_cons_succ]; push_cast; linarith
      · rw [arrivalEpoch_cons_succ]; push_cast; linarith
  · simp only [firstPass, mem_ofPred_eq, mem_empty_iff_false, iff_false, not_and]
    intro h1
    exfalso
    have := h1 0 (Nat.succ_pos n)
    simp only [arrivalEpoch_cons_zero, Nat.cast_zero, sub_zero] at this
    exact h this

lemma law_firstPass_succ (f x : ℝ) (n : ℕ) :
    interarrivalLaw (firstPass f x (n + 1)) =
      ∫⁻ a, (if f * a ≤ x then interarrivalLaw (firstPass f (x + 1 - f * a) n) else 0)
        ∂(expMeasure 1) := by
  conv_lhs => rw [← law_shift]
  rw [Measure.map_apply measurable_consPath (measurableSet_firstPass _ _ _),
    Measure.prod_apply (measurable_consPath (measurableSet_firstPass _ _ _))]
  apply lintegral_congr
  intro a
  have : Prod.mk a ⁻¹' (consPath ⁻¹' firstPass f x (n + 1)) =
      {ξ | consPath (a, ξ) ∈ firstPass f x (n + 1)} := rfl
  rw [this, firstPass_cons]
  split_ifs <;> simp

lemma law_firstPass_zero (f x : ℝ) (hf : 0 < f) (hx : 0 ≤ x) :
    interarrivalLaw (firstPass f x 0) = ENNReal.ofReal (poisMass (x / f) 0) := by
  have hset : firstPass f x 0 = (fun ξ : DemandPath => ξ 0) ⁻¹' Ioi (x / f) := by
    ext ξ
    have h0 : arrivalEpoch ξ 0 = ξ 0 := by simp [arrivalEpoch]
    simp only [firstPass, mem_ofPred_eq, Set.mem_preimage, mem_Ioi, h0, Nat.cast_zero, sub_zero]
    constructor
    · rintro ⟨-, h⟩; rw [div_lt_iff₀ hf]; linarith
    · intro h
      refine ⟨fun k hk => absurd hk (Nat.not_lt_zero k), ?_⟩
      rw [div_lt_iff₀ hf] at h; linarith
  have hmap : interarrivalLaw.map (fun ξ : DemandPath => ξ 0) = expMeasure 1 := by
    unfold interarrivalLaw; exact Measure.infinitePi_map_eval (fun _ : ℕ => expMeasure 1) 0
  rw [hset, ← Measure.map_apply (measurable_pi_apply 0) measurableSet_Ioi, hmap,
    exp_Ioi (x / f) (div_nonneg hx hf.le)]
  congr 1
  unfold poisMass; simp

/-- Closed form of the first-passage probability: p_n(t) - p_{n-1}(t)/f with t = (x+n)/f. -/
noncomputable def kend (f x : ℝ) (n : ℕ) : ℝ :=
  poisMass ((x + n) / f) n - pPrev n ((x + n) / f) / f

lemma continuous_kend (f : ℝ) (n : ℕ) : Continuous (fun x => kend f x n) := by
  unfold kend
  have h1 : Continuous (fun x : ℝ => (x + n) / f) := by fun_prop
  exact ((continuous_pm n).comp h1).sub (((continuous_pPrev n).comp h1).div_const f)

lemma kend_nonneg (f y : ℝ) (hf : 0 < f) (hy : 0 ≤ y) (n : ℕ) : 0 ≤ kend f y n := by
  unfold kend
  have ht : 0 ≤ (y + n) / f := div_nonneg (by positivity) hf.le
  cases n with
  | zero => simp only [pPrev, zero_div, sub_zero]; exact d2_pm_nonneg _ ht 0
  | succ k =>
    simp only [pPrev]
    set t := (y + ((k + 1 : ℕ) : ℝ)) / f with htdef
    have hp := pm_succ t k
    have hk1 : (0:ℝ) < (k:ℝ) + 1 := by positivity
    have hpk := d2_pm_nonneg t ht k
    have hft : f * t = y + (k + 1) := by rw [htdef]; push_cast; field_simp
    -- p_{k+1}(t) = t p_k(t)/(k+1) ≥ ((k+1)/f) p_k(t)/(k+1) = p_k/f
    have h1 : poisMass t (k + 1) * ((k:ℝ) + 1) * f = t * f * poisMass t k := by rw [hp]; ring
    have h2 : poisMass t k / f * ((k:ℝ) + 1) * f = ((k:ℝ) + 1) * poisMass t k := by
      field_simp
    have h3 : ((k:ℝ) + 1) * poisMass t k ≤ t * f * poisMass t k := by
      apply mul_le_mul_of_nonneg_right _ hpk; nlinarith
    have h4 : poisMass t k / f * (((k:ℝ) + 1) * f) ≤ poisMass t (k + 1) * (((k:ℝ) + 1) * f) := by
      nlinarith
    have := le_of_mul_le_mul_right h4 (by positivity)
    linarith

lemma lint_exp_Iic_eq (h : ℝ) (hh : 0 ≤ h) (G : ℝ → ℝ) (hGc : Continuous G)
    (hG0 : ∀ a ∈ Icc 0 h, 0 ≤ G a) :
    ∫⁻ a in Iic h, ENNReal.ofReal (G a) ∂(expMeasure 1) =
      ENNReal.ofReal (∫ a in (0:ℝ)..h, Real.exp (-a) * G a) := by
  rw [expMeasure_eq_withDensity, setLIntegral_withDensity_eq_setLIntegral_mul _
    (measurable_exponentialPDF' 1) hGc.measurable.ennreal_ofReal measurableSet_Iic]
  have h1 : ∫⁻ a in Iic h, (exponentialPDF 1 * fun a => ENNReal.ofReal (G a)) a =
      ∫⁻ a in Icc 0 h, ENNReal.ofReal (Real.exp (-a) * G a) := by
    rw [← lintegral_indicator measurableSet_Iic, ← lintegral_indicator measurableSet_Icc]
    apply lintegral_congr
    intro a
    by_cases ha : 0 ≤ a
    · by_cases hah : a ≤ h
      · rw [indicator_of_mem (show a ∈ Iic h from hah),
          indicator_of_mem (show a ∈ Icc 0 h from ⟨ha, hah⟩)]
        simp only [Pi.mul_apply]
        rw [exponentialPDF_of_nonneg ha, ← ENNReal.ofReal_mul (by positivity)]
        congr 1; ring
      · rw [indicator_of_notMem (show a ∉ Iic h by simpa using hah),
          indicator_of_notMem (show a ∉ Icc 0 h by simp [hah])]
    · push Not at ha
      rw [indicator_of_notMem (show a ∉ Icc 0 h by simp [not_le.mpr ha])]
      by_cases hah : a ≤ h
      · rw [indicator_of_mem (show a ∈ Iic h from hah)]
        simp [Pi.mul_apply, exponentialPDF_of_neg ha]
      · rw [indicator_of_notMem (show a ∉ Iic h by simpa using hah)]
  rw [h1, intervalIntegral.integral_of_le hh, ← integral_Icc_eq_integral_Ioc,
    ofReal_integral_eq_lintegral_ofReal]
  · exact ((Real.continuous_exp.comp continuous_neg).mul hGc).integrableOn_Icc
  · filter_upwards [ae_restrict_mem measurableSet_Icc] with a ha
    exact mul_nonneg (Real.exp_pos _).le (hG0 a ha)

lemma kend_ftc (f x : ℝ) (hf : 0 < f) (hx : 0 ≤ x) (n : ℕ) :
    ∫ a in (0:ℝ)..(x / f), Real.exp (-a) * kend f (x + 1 - f * a) n = kend f x (n + 1) := by
  set t := (x + n + 1) / f with ht
  have hderiv : ∀ a, HasDerivAt
      (fun b => Real.exp (-b) * (poisMass (t - b) n / f - poisMass (t - b) (n + 1)))
      (Real.exp (-a) * kend f (x + 1 - f * a) n) a := by
    intro a
    have hsub : HasDerivAt (fun b : ℝ => t - b) (-1) a := by
      simpa using (hasDerivAt_id a).const_sub t
    have hp1 := (hasDerivAt_pm n (t - a)).comp a hsub
    have hp2 := (hasDerivAt_pm (n + 1) (t - a)).comp a hsub
    have he := (hasDerivAt_neg a).exp
    have hh := he.mul ((hp1.div_const f).sub hp2)
    refine hh.congr_deriv ?_
    have harg : (x + 1 - f * a + n) / f = t - a := by rw [ht]; field_simp; ring
    have hpp : pPrev (n + 1) (t - a) = poisMass (t - a) n := rfl
    have hk : kend f (x + 1 - f * a) n = poisMass (t - a) n - pPrev n (t - a) / f := by
      unfold kend; rw [harg]
    simp only [Pi.sub_apply, Function.comp_apply, hpp, hk]
    ring
  have hint : IntervalIntegrable (fun a => Real.exp (-a) * kend f (x + 1 - f * a) n)
      volume 0 (x / f) := by
    apply Continuous.intervalIntegrable
    exact (Real.continuous_exp.comp continuous_neg).mul
      ((continuous_kend f n).comp (by fun_prop))
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun a _ => hderiv a) hint]
  have h1 : t - x / f = ((n:ℝ) + 1) / f := by rw [ht]; field_simp; ring
  have hn1 : (0:ℝ) < (n:ℝ) + 1 := by positivity
  have h2 : poisMass (((n:ℝ) + 1) / f) (n + 1) = poisMass (((n:ℝ) + 1) / f) n / f := by
    have hp : poisMass (((n:ℝ) + 1) / f) (n + 1) =
        ((n:ℝ) + 1) / f * poisMass (((n:ℝ) + 1) / f) n / ((n:ℝ) + 1) := by
      rw [eq_div_iff hn1.ne', pm_succ]
    rw [hp]; field_simp
  simp only [h1, sub_zero, h2, sub_self, mul_zero, zero_sub]
  simp only [kend, pPrev]
  push_cast
  have h3 : (x + ((n:ℝ) + 1)) / f = t := by rw [ht]; ring
  rw [h3]
  simp only [neg_zero, Real.exp_zero, one_mul]
  ring

lemma law_firstPass (f : ℝ) (hf : 0 < f) (n : ℕ) :
    ∀ x : ℝ, 0 ≤ x → interarrivalLaw (firstPass f x n) = ENNReal.ofReal (kend f x n) := by
  induction n with
  | zero =>
    intro x hx
    rw [law_firstPass_zero f x hf hx]
    congr 1
    simp [kend, pPrev]
  | succ n ih =>
    intro x hx
    rw [law_firstPass_succ]
    have h1 : ∀ a, (if f * a ≤ x then interarrivalLaw (firstPass f (x + 1 - f * a) n) else 0) =
        (Iic (x / f)).indicator (fun a => ENNReal.ofReal (kend f (x + 1 - f * a) n)) a := by
      intro a
      by_cases ha : f * a ≤ x
      · have : a ∈ Iic (x / f) := by rw [mem_Iic, le_div_iff₀ hf]; linarith
        rw [if_pos ha, indicator_of_mem this, ih _ (by linarith)]
      · have : a ∉ Iic (x / f) := by
          rw [mem_Iic, le_div_iff₀ hf]; push Not at ha ⊢; linarith
        rw [if_neg ha, indicator_of_notMem this]
    simp_rw [h1]
    rw [lintegral_indicator measurableSet_Iic,
      lint_exp_Iic_eq (x / f) (div_nonneg hx hf.le) (fun a => kend f (x + 1 - f * a) n)
        ((continuous_kend f n).comp (by fun_prop))
        (fun a ha => kend_nonneg f _ hf (by
          have : f * a ≤ x := by have := ha.2; rw [le_div_iff₀ hf] at this; linarith
          linarith) n),
      kend_ftc f x hf hx n]

end LostSalesRQ

namespace LostSalesRQ

open MeasureTheory ProbabilityTheory Filter Set Topology

/-- A measurable version of the maximal excess: sup_k (min (f S_k) (f μ) - k). -/
noncomputable def maxDisc (μ f : ℝ) (ξ : DemandPath) : ℝ :=
  ⨆ k : ℕ, (min (f * arrivalEpoch ξ k) (f * μ) - k)

lemma maxDisc_bdd (μ f : ℝ) (ξ : DemandPath) :
    BddAbove (Set.range fun k : ℕ => min (f * arrivalEpoch ξ k) (f * μ) - k) := by
  refine ⟨f * μ, ?_⟩
  rintro _ ⟨k, rfl⟩
  have : (0:ℝ) ≤ k := Nat.cast_nonneg k
  have := min_le_right (f * arrivalEpoch ξ k) (f * μ)
  linarith

lemma measurable_maxDisc (μ f : ℝ) : Measurable (maxDisc μ f) := by
  unfold maxDisc
  exact Measurable.iSup (fun k =>
    (((measurable_arrivalEpoch k).const_mul f).min measurable_const).sub_const _)

lemma maxDisc_le (μ f : ℝ) (ξ : DemandPath) : maxDisc μ f ξ ≤ f * μ :=
  ciSup_le (fun k => by
    have : (0:ℝ) ≤ k := Nat.cast_nonneg k
    have := min_le_right (f * arrivalEpoch ξ k) (f * μ)
    linarith)

lemma maxDisc_nonneg (μ f : ℝ) (hμ : 0 ≤ μ) (hf : 0 ≤ f) (ξ : DemandPath) (hξ : 0 ≤ ξ 0) :
    0 ≤ maxDisc μ f ξ := by
  have h0 : arrivalEpoch ξ 0 = ξ 0 := by simp [arrivalEpoch]
  have := le_ciSup (maxDisc_bdd μ f ξ) 0
  simp only [h0, Nat.cast_zero, sub_zero] at this
  exact le_trans (le_min (mul_nonneg hf hξ) (mul_nonneg hf hμ)) this

lemma lt_maxDisc_iff (μ f x : ℝ) (ξ : DemandPath) :
    x < maxDisc μ f ξ ↔ ∃ n, ξ ∈ firstPass f x n ∧ x + n < f * μ := by
  constructor
  · intro h
    obtain ⟨k, hk⟩ := exists_lt_of_lt_ciSup h
    have h1 : x < f * arrivalEpoch ξ k - k := by
      have := min_le_left (f * arrivalEpoch ξ k) (f * μ); linarith
    have h2 : x < f * μ - k := by
      have := min_le_right (f * arrivalEpoch ξ k) (f * μ); linarith
    classical
    have hex : ∃ j, x < f * arrivalEpoch ξ j - j := ⟨k, h1⟩
    refine ⟨Nat.find hex, ⟨fun j hj => ?_, Nat.find_spec hex⟩, ?_⟩
    · have := Nat.find_min hex hj; push Not at this; exact this
    · have h3 : Nat.find hex ≤ k := Nat.find_min' hex h1
      have h4 : ((Nat.find hex : ℕ) : ℝ) ≤ k := by exact_mod_cast h3
      linarith
  · rintro ⟨n, ⟨-, hn⟩, hxn⟩
    apply lt_of_lt_of_le _ (le_ciSup (maxDisc_bdd μ f ξ) n)
    have : x + n < min (f * arrivalEpoch ξ n) (f * μ) := lt_min (by linarith) hxn
    show x < min (f * arrivalEpoch ξ n) (f * μ) - n
    linarith

lemma firstPass_disjoint (f x : ℝ) (i j : ℕ) (hij : i ≠ j) :
    Disjoint (firstPass f x i) (firstPass f x j) := by
  rw [Set.disjoint_left]
  rintro ξ ⟨hi1, hi2⟩ ⟨hj1, hj2⟩
  rcases lt_or_gt_of_ne hij with h | h
  · have := hj1 i h; linarith
  · have := hi1 j h; linarith

/-- Paths with nonnegative interarrival times, a positive first one, and an arrival after μ. -/
def goodSet (μ : ℝ) : Set DemandPath :=
  {ξ | (∀ i, 0 ≤ ξ i) ∧ 0 < ξ 0 ∧ ∃ K, μ < arrivalEpoch ξ K}

lemma law_first_nonpos : interarrivalLaw {ξ : DemandPath | ξ 0 ≤ 0} = 0 := by
  have hmap : interarrivalLaw.map (fun ξ : DemandPath => ξ 0) = expMeasure 1 := by
    unfold interarrivalLaw; exact Measure.infinitePi_map_eval (fun _ : ℕ => expMeasure 1) 0
  have : {ξ : DemandPath | ξ 0 ≤ 0} = (fun ξ : DemandPath => ξ 0) ⁻¹' Iic 0 := rfl
  rw [this, ← Measure.map_apply (measurable_pi_apply 0) measurableSet_Iic, hmap,
    exp_Iic 1 0 one_pos le_rfl]
  simp

lemma ae_goodSet (μ : ℝ) : ∀ᵐ ξ ∂interarrivalLaw, ξ ∈ goodSet μ := by
  rw [ae_iff]
  have hsub : {ξ : DemandPath | ¬ ξ ∈ goodSet μ} ⊆ badSet μ ∪ {ξ : DemandPath | ξ 0 ≤ 0} := by
    intro ξ hξ
    by_contra hc
    simp only [mem_union, mem_ofPred_eq, not_or, not_le] at hc
    apply hξ
    obtain ⟨hb, h0⟩ := hc
    simp only [badSet, mem_ofPred_eq, not_not] at hb
    exact ⟨hb.1, h0, hb.2⟩
  refine le_antisymm ?_ zero_le
  calc interarrivalLaw {ξ : DemandPath | ¬ ξ ∈ goodSet μ}
      ≤ interarrivalLaw (badSet μ ∪ {ξ : DemandPath | ξ 0 ≤ 0}) := measure_mono hsub
    _ ≤ interarrivalLaw (badSet μ) + interarrivalLaw {ξ : DemandPath | ξ 0 ≤ 0} :=
        measure_union_le _ _
    _ = 0 := by rw [law_badSet, law_first_nonpos, add_zero]

lemma arrivalEpoch_mono (ξ : DemandPath) (hpos : ∀ i, 0 ≤ ξ i) : Monotone (arrivalEpoch ξ) := by
  apply monotone_nat_of_le_succ; intro k; unfold arrivalEpoch
  rw [Finset.sum_range_succ _ (k + 1)]; linarith [hpos (k + 1)]

lemma excess_le_disc (μ f : ℝ) (hf : 0 ≤ f) (ξ : DemandPath) (hpos : ∀ i, 0 ≤ ξ i)
    (hK : ∃ K, μ < arrivalEpoch ξ K) (t : ℝ) (htμ : t ≤ μ) :
    f * t - (unitCount ξ t : ℝ) ≤ maxDisc μ f ξ := by
  have hmono := arrivalEpoch_mono ξ hpos
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
  have htm : t < arrivalEpoch ξ m := by
    simp only [hD, mem_ofPred_eq, not_le] at hmD; exact hmD
  have hN : (unitCount ξ t : ℝ) = m := rfl
  rw [hN]
  refine le_trans ?_ (le_ciSup (maxDisc_bdd μ f ξ) m)
  have h1 : f * t ≤ f * arrivalEpoch ξ m := mul_le_mul_of_nonneg_left htm.le hf
  have h2 : f * t ≤ f * μ := mul_le_mul_of_nonneg_left htμ hf
  have := le_min h1 h2
  show f * t - m ≤ min (f * arrivalEpoch ξ m) (f * μ) - m
  linarith

lemma maxExcess_bdd (μ f : ℝ) (hf : 0 ≤ f) (ξ : DemandPath) :
    BddAbove ((fun t : ℝ => f * t - (unitCount ξ t : ℝ)) '' Icc 0 μ) := by
  refine ⟨f * μ, ?_⟩
  rintro _ ⟨s, ⟨hs0, hsμ⟩, rfl⟩
  have : (0:ℝ) ≤ unitCount ξ s := Nat.cast_nonneg _
  have : f * s ≤ f * μ := mul_le_mul_of_nonneg_left hsμ hf
  linarith

lemma disc_term_lt_excess (μ f x : ℝ) (hf : 0 ≤ f) (hx : 0 ≤ x) (ξ : DemandPath)
    (hpos : ∀ i, 0 ≤ ξ i) (k : ℕ) (h1 : x < f * arrivalEpoch ξ k - k) (h2 : x < f * μ - k) :
    x < maxExcess μ f ξ := by
  have hk0 : (0:ℝ) ≤ k := Nat.cast_nonneg k
  have hfpos : 0 < f := by
    rcases hf.eq_or_lt with h | h
    · rw [← h, zero_mul, zero_sub] at h2; linarith
    · exact h
  have hmono := arrivalEpoch_mono ξ hpos
  set u := min (arrivalEpoch ξ k) μ with hu
  have hlo : (x + k) / f < u :=
    lt_min (by rw [div_lt_iff₀ hfpos]; linarith) (by rw [div_lt_iff₀ hfpos]; linarith)
  set t := ((x + k) / f + u) / 2 with htdef
  have ht1 : (x + k) / f < t := by linarith
  have ht2 : t < u := by linarith
  have ht0 : 0 ≤ t := le_trans (div_nonneg (by positivity) hfpos.le) ht1.le
  have htμ : t ≤ μ := le_trans ht2.le (min_le_right _ _)
  have htS : t < arrivalEpoch ξ k := lt_of_lt_of_le ht2 (min_le_left _ _)
  have hN : unitCount ξ t ≤ k := by
    unfold unitCount
    have hsub : {j : ℕ | arrivalEpoch ξ j ≤ t} ⊆ ↑(Finset.range k) := by
      intro j hj
      simp only [mem_ofPred_eq] at hj
      simp only [Finset.coe_range, mem_Iio]
      by_contra hjk; push Not at hjk
      have := hmono hjk; linarith
    have := Set.ncard_le_ncard hsub (Finset.finite_toSet _)
    rwa [Set.ncard_coe_finset, Finset.card_range] at this
  have hNr : (unitCount ξ t : ℝ) ≤ k := by exact_mod_cast hN
  have hval : x < f * t - unitCount ξ t := by
    have : x + k < f * t := by rw [div_lt_iff₀ hfpos] at ht1; linarith
    linarith
  unfold maxExcess
  exact lt_of_lt_of_le hval (le_csSup (maxExcess_bdd μ f hf ξ) ⟨t, ⟨ht0, htμ⟩, rfl⟩)

lemma maxExcess_eq_maxDisc (μ f : ℝ) (hμ : 0 ≤ μ) (hf : 0 ≤ f) (ξ : DemandPath)
    (hξ : ξ ∈ goodSet μ) : maxExcess μ f ξ = maxDisc μ f ξ := by
  obtain ⟨hpos, h0, hK⟩ := hξ
  have hmono := arrivalEpoch_mono ξ hpos
  have hne : ((fun t : ℝ => f * t - (unitCount ξ t : ℝ)) '' Icc 0 μ).Nonempty :=
    ⟨_, 0, ⟨le_rfl, hμ⟩, rfl⟩
  have hN0 : unitCount ξ 0 = 0 := by
    unfold unitCount
    have : {k : ℕ | arrivalEpoch ξ k ≤ 0} = ∅ := by
      ext k
      simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false, not_le]
      calc 0 < ξ 0 := h0
        _ = arrivalEpoch ξ 0 := by simp [arrivalEpoch]
        _ ≤ arrivalEpoch ξ k := hmono (Nat.zero_le k)
    rw [this, Set.ncard_empty]
  have hM0 : 0 ≤ maxExcess μ f ξ := by
    unfold maxExcess
    refine le_trans ?_ (le_csSup (maxExcess_bdd μ f hf ξ) ⟨0, ⟨le_rfl, hμ⟩, rfl⟩)
    simp [hN0]
  apply le_antisymm
  · unfold maxExcess
    apply csSup_le hne
    rintro _ ⟨t, ⟨ht0, htμ⟩, rfl⟩
    exact excess_le_disc μ f hf ξ hpos hK t htμ
  · unfold maxDisc
    apply ciSup_le
    intro k
    by_contra hlt; push Not at hlt
    have h1 : maxExcess μ f ξ < f * arrivalEpoch ξ k - k := by
      have := min_le_left (f * arrivalEpoch ξ k) (f * μ); linarith
    have h2 : maxExcess μ f ξ < f * μ - k := by
      have := min_le_right (f * arrivalEpoch ξ k) (f * μ); linarith
    have := disc_term_lt_excess μ f (maxExcess μ f ξ) hf hM0 ξ hpos k h1 h2
    exact lt_irrefl _ this

lemma ae_maxExcess_eq (μ f : ℝ) (hμ : 0 ≤ μ) (hf : 0 ≤ f) :
    ∀ᵐ ξ ∂interarrivalLaw, maxExcess μ f ξ = maxDisc μ f ξ := by
  filter_upwards [ae_goodSet μ] with ξ hξ
  exact maxExcess_eq_maxDisc μ f hμ hf ξ hξ

lemma law_lt_maxDisc (μ f x : ℝ) (hμ : 0 ≤ μ) (hf : 0 ≤ f) (hx : 0 < x) :
    interarrivalLaw {ξ | x < maxDisc μ f ξ} =
      ∑ n ∈ Finset.range ⌈f * μ⌉₊,
        (Iio (f * μ - n)).indicator (fun y => ENNReal.ofReal (kend f y n)) x := by
  classical
  have hset : {ξ | x < maxDisc μ f ξ} =
      ⋃ n ∈ (Finset.range ⌈f * μ⌉₊).filter (fun n : ℕ => x + n < f * μ), firstPass f x n := by
    ext ξ
    simp only [mem_ofPred_eq, mem_iUnion, Finset.mem_filter, Finset.mem_range, exists_prop]
    rw [lt_maxDisc_iff]
    constructor
    · rintro ⟨n, hn, hxn⟩
      refine ⟨n, ⟨?_, hxn⟩, hn⟩
      rw [Nat.lt_ceil]; linarith
    · rintro ⟨n, ⟨-, hxn⟩, hn⟩; exact ⟨n, hn, hxn⟩
  rw [hset, measure_biUnion_finset]
  · rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro n _
    by_cases hxn : x + n < f * μ
    · have hfpos : 0 < f := by
        rcases hf.eq_or_lt with h | h
        · rw [← h, zero_mul] at hxn
          have : (0:ℝ) ≤ n := Nat.cast_nonneg n
          linarith
        · exact h
      rw [if_pos hxn, indicator_of_mem (show x ∈ Iio (f * μ - n) by rw [mem_Iio]; linarith),
        law_firstPass f hfpos n x hx.le]
    · rw [if_neg hxn, indicator_of_notMem (show x ∉ Iio (f * μ - n) by
        rw [mem_Iio]; push Not at hxn ⊢; linarith)]
  · intro i _ j _ hij
    exact firstPass_disjoint f x i j hij
  · intro n _; exact measurableSet_firstPass f x n

lemma integral_maxDisc (μ f : ℝ) (hμ : 0 ≤ μ) (hf : 0 ≤ f) :
    ∫ ξ, maxDisc μ f ξ ∂interarrivalLaw =
      ∑ n ∈ Finset.range ⌈f * μ⌉₊, ∫ y in (0:ℝ)..(f * μ - n), kend f y n := by
  have hnn : 0 ≤ᵐ[interarrivalLaw] maxDisc μ f := by
    filter_upwards [ae_goodSet μ] with ξ hξ
    exact maxDisc_nonneg μ f hμ hf ξ hξ.2.1.le
  rw [integral_eq_lintegral_of_nonneg_ae hnn (measurable_maxDisc μ f).aestronglyMeasurable,
    lintegral_eq_lintegral_meas_lt _ hnn (measurable_maxDisc μ f).aemeasurable,
    setLIntegral_congr_fun measurableSet_Ioi (fun x hx => law_lt_maxDisc μ f x hμ hf hx),
    lintegral_finsetSum _ (fun n _ =>
      ((continuous_kend f n).measurable.ennreal_ofReal).indicator measurableSet_Iio)]
  have hterm : ∀ n ∈ Finset.range ⌈f * μ⌉₊,
      ∫⁻ x in Ioi 0, (Iio (f * μ - n)).indicator (fun y => ENNReal.ofReal (kend f y n)) x =
        ENNReal.ofReal (∫ y in (0:ℝ)..(f * μ - n), kend f y n) := by
    intro n hn
    have hlt : (n : ℝ) < f * μ := Nat.lt_ceil.mp (Finset.mem_range.mp hn)
    have hfpos : 0 < f := by
      rcases hf.eq_or_lt with h | h
      · rw [← h, zero_mul] at hlt
        have : (0:ℝ) ≤ n := Nat.cast_nonneg n
        linarith
      · exact h
    have hb : 0 ≤ f * μ - n := by linarith
    rw [lintegral_indicator measurableSet_Iio, Measure.restrict_restrict measurableSet_Iio]
    rw [show Iio (f * μ - n) ∩ Ioi 0 = Ioo 0 (f * μ - n) by ext; simp [and_comm]]
    rw [intervalIntegral.integral_of_le hb, ofReal_integral_eq_lintegral_ofReal]
    · exact setLIntegral_congr Ioo_ae_eq_Ioc
    · exact ((continuous_kend f n).integrableOn_Icc).mono_set Ioc_subset_Icc_self
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with y hy
      exact kend_nonneg f y hfpos hy.1.le n
  rw [Finset.sum_congr rfl hterm, ← ENNReal.ofReal_sum_of_nonneg, ENNReal.toReal_ofReal]
  · apply Finset.sum_nonneg
    intro n hn
    have hlt : (n : ℝ) < f * μ := Nat.lt_ceil.mp (Finset.mem_range.mp hn)
    have hfpos : 0 < f := by
      rcases hf.eq_or_lt with h | h
      · rw [← h, zero_mul] at hlt
        have : (0:ℝ) ≤ n := Nat.cast_nonneg n
        linarith
      · exact h
    apply intervalIntegral.integral_nonneg (by linarith)
    intro y hy
    exact kend_nonneg f y hfpos hy.1 n
  · intro n hn
    have hlt : (n : ℝ) < f * μ := Nat.lt_ceil.mp (Finset.mem_range.mp hn)
    have hfpos : 0 < f := by
      rcases hf.eq_or_lt with h | h
      · rw [← h, zero_mul] at hlt
        have : (0:ℝ) ≤ n := Nat.cast_nonneg n
        linarith
      · exact h
    apply intervalIntegral.integral_nonneg (by linarith)
    intro y hy
    exact kend_nonneg f y hfpos hy.1 n

end LostSalesRQ

namespace LostSalesRQ

open MeasureTheory ProbabilityTheory Filter Set Topology

lemma kend_integral (η μ : ℝ) (hη : 1 ≤ η) (n : ℕ) (hn : (n : ℝ) < (1 - 1 / η) * μ) :
    ∫ y in (0:ℝ)..((1 - 1 / η) * μ - n), kend (1 - 1 / η) y n =
      (wfun η n (n / (1 - 1 / η)) - wfun η n μ) / η := by
  have hη0 : 0 < η := by linarith
  have hfη : η * (1 - 1 / η) = η - 1 := by field_simp
  have hf0 : 0 ≤ 1 - 1 / η := by rw [sub_nonneg, div_le_one hη0]; exact hη
  have hfpos : 0 < 1 - 1 / η := by
    rcases hf0.eq_or_lt with h | h
    · rw [← h, zero_mul] at hn
      have : (0:ℝ) ≤ n := Nat.cast_nonneg n
      linarith
    · exact h
  set f := 1 - 1 / η with hfdef
  have hf0' : f ≠ 0 := hfpos.ne'
  have hη0' : η ≠ 0 := hη0.ne'
  have hderiv : ∀ y, HasDerivAt (fun y => -wfun η n ((y + n) / f) / η) (kend f y n) y := by
    intro y
    have hin : HasDerivAt (fun y : ℝ => (y + n) / f) (1 / f) y := by
      simpa using ((hasDerivAt_id y).add_const (n:ℝ)).div_const f
    have h := ((hasDerivAt_wfun η n ((y + n) / f)).comp y hin).neg.div_const η
    refine h.congr_deriv ?_
    unfold kend
    set A := pPrev n ((y + n) / f)
    set P := poisMass ((y + n) / f) n
    have key : -((η * (A - P) + P) * (1 / f)) / η - (P - A / f) =
        P * (η - 1 - η * f) / (f * η) := by
      field_simp; ring
    rw [hfη, sub_self, mul_zero, zero_div] at key
    linarith
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun y _ => hderiv y)
    ((continuous_kend f n).intervalIntegrable _ _)]
  have h1 : (f * μ - n + n) / f = μ := by field_simp; ring
  have h2 : ((0:ℝ) + n) / f = n / f := by ring
  simp only [h1, h2]
  ring

lemma eta_mul_expectedMaxExcess (μ η : ℝ) (hμ : 0 ≤ μ) (hη : 1 ≤ η) :
    η * expectedMaxExcess μ (1 / η) =
      ∑ n ∈ Finset.range ⌈(1 - 1 / η) * μ⌉₊, (wfun η n (n / (1 - 1 / η)) - wfun η n μ) := by
  have hη0 : 0 < η := by linarith
  have hf0 : 0 ≤ 1 - 1 / η := by rw [sub_nonneg, div_le_one hη0]; exact hη
  unfold expectedMaxExcess
  rw [integral_congr_ae (ae_maxExcess_eq μ (1 - 1 / η) hμ hf0),
    integral_maxDisc μ (1 - 1 / η) hμ hf0, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  rw [kend_integral η μ hη n (Nat.lt_ceil.mp (Finset.mem_range.mp hn))]
  field_simp

lemma calibration_identity (μ η : ℝ) (hμ : 0 ≤ μ) (hη : 1 ≤ η) :
    rankBound μ η + agingRateSup μ η = calibratedPenalty μ η := by
  rw [calib_analytic μ η hμ hη, ← eta_mul_expectedMaxExcess μ η hμ hη]
  unfold calibratedPenalty
  ring

/-- Expected maximal excess as a function of the slope f. -/
noncomputable def Wf (μ f : ℝ) : ℝ := ∫ ξ, maxExcess μ f ξ ∂interarrivalLaw

lemma expectedMaxExcess_eq_Wf (μ η : ℝ) : expectedMaxExcess μ (1 / η) = Wf μ (1 - 1 / η) := rfl

lemma integrable_maxExcess (μ f : ℝ) (hμ : 0 ≤ μ) (hf : 0 ≤ f) :
    Integrable (maxExcess μ f) interarrivalLaw := by
  have hd : Integrable (maxDisc μ f) interarrivalLaw := by
    refine (integrable_const (f * μ)).mono' (measurable_maxDisc μ f).aestronglyMeasurable ?_
    filter_upwards [ae_goodSet μ] with ξ hξ
    have h1 := maxDisc_nonneg μ f hμ hf ξ hξ.2.1.le
    have h2 := maxDisc_le μ f ξ
    rw [Real.norm_eq_abs, abs_le]
    constructor <;> linarith
  have he : maxDisc μ f =ᵐ[interarrivalLaw] maxExcess μ f := by
    filter_upwards [ae_maxExcess_eq μ f hμ hf] with ξ h
    exact h.symm
  exact hd.congr he

lemma maxExcess_mono (μ f f' : ℝ) (hμ : 0 ≤ μ) (hf : 0 ≤ f) (hff' : f ≤ f') (ξ : DemandPath) :
    maxExcess μ f ξ ≤ maxExcess μ f' ξ := by
  unfold maxExcess
  apply csSup_le ((Set.nonempty_Icc.mpr hμ).image _)
  rintro _ ⟨t, ⟨ht0, htμ⟩, rfl⟩
  refine le_trans ?_ (le_csSup (maxExcess_bdd μ f' (hf.trans hff') ξ) ⟨t, ⟨ht0, htμ⟩, rfl⟩)
  have := mul_le_mul_of_nonneg_right hff' ht0
  show f * t - (unitCount ξ t : ℝ) ≤ f' * t - (unitCount ξ t : ℝ)
  linarith

lemma maxExcess_lip (μ f f' : ℝ) (hμ : 0 ≤ μ) (hf : 0 ≤ f) (hff' : f ≤ f') (ξ : DemandPath) :
    maxExcess μ f' ξ ≤ maxExcess μ f ξ + (f' - f) * μ := by
  unfold maxExcess
  apply csSup_le ((Set.nonempty_Icc.mpr hμ).image _)
  rintro _ ⟨t, ⟨ht0, htμ⟩, rfl⟩
  have h1 := le_csSup (maxExcess_bdd μ f hf ξ) ⟨t, ⟨ht0, htμ⟩, rfl⟩
  have h2 : (f' - f) * t ≤ (f' - f) * μ := mul_le_mul_of_nonneg_left htμ (by linarith)
  show f' * t - (unitCount ξ t : ℝ) ≤ _
  have h3 : f' * t - (unitCount ξ t : ℝ) = (f * t - (unitCount ξ t : ℝ)) + (f' - f) * t := by ring
  rw [h3]
  exact add_le_add h1 h2

lemma Wf_mono (μ f f' : ℝ) (hμ : 0 ≤ μ) (hf : 0 ≤ f) (hff' : f ≤ f') : Wf μ f ≤ Wf μ f' :=
  integral_mono (integrable_maxExcess μ f hμ hf) (integrable_maxExcess μ f' hμ (hf.trans hff'))
    (fun ξ => maxExcess_mono μ f f' hμ hf hff' ξ)

lemma Wf_lip (μ f f' : ℝ) (hμ : 0 ≤ μ) (hf : 0 ≤ f) (hff' : f ≤ f') :
    Wf μ f' ≤ Wf μ f + (f' - f) * μ := by
  have hint2 : Integrable (fun ξ => maxExcess μ f ξ + (f' - f) * μ) interarrivalLaw :=
    (integrable_maxExcess μ f hμ hf).add (integrable_const ((f' - f) * μ))
  have h : ∫ ξ, maxExcess μ f' ξ ∂interarrivalLaw ≤
      ∫ ξ, (maxExcess μ f ξ + (f' - f) * μ) ∂interarrivalLaw :=
    integral_mono (integrable_maxExcess μ f' hμ (hf.trans hff')) hint2
      (fun ξ => maxExcess_lip μ f f' hμ hf hff' ξ)
  rw [integral_add (integrable_maxExcess μ f hμ hf) (integrable_const _), integral_const] at h
  simpa [Wf] using h

lemma Wf_nonneg (μ f : ℝ) (hμ : 0 ≤ μ) (hf : 0 ≤ f) : 0 ≤ Wf μ f := by
  apply integral_nonneg_of_ae
  filter_upwards [ae_goodSet μ, ae_maxExcess_eq μ f hμ hf] with ξ hξ heq
  rw [Pi.zero_apply, heq]
  exact maxDisc_nonneg μ f hμ hf ξ hξ.2.1.le

lemma Wf_zero (μ : ℝ) (hμ : 0 ≤ μ) : Wf μ 0 = 0 := by
  have := eta_mul_expectedMaxExcess μ 1 hμ le_rfl
  rw [expectedMaxExcess_eq_Wf] at this
  simpa using this

lemma calibratedPenalty_eq (μ η : ℝ) : calibratedPenalty μ η = η * (1 + Wf μ (1 - 1 / η)) := rfl

lemma calibratedPenalty_continuousOn (μ : ℝ) (hμ : 0 ≤ μ) :
    ContinuousOn (calibratedPenalty μ) (Ici 1) := by
  have hWlip : LipschitzOnWith (Real.toNNReal μ) (fun f => Wf μ f) (Icc 0 1) := by
    apply LipschitzOnWith.of_dist_le'
    intro f hf f' hf'
    rw [Real.dist_eq, Real.dist_eq]
    rcases le_total f f' with h | h
    · have h1 := Wf_mono μ f f' hμ hf.1 h
      have h2 := Wf_lip μ f f' hμ hf.1 h
      rw [abs_sub_comm, abs_of_nonneg (by linarith), abs_sub_comm, abs_of_nonneg (by linarith)]
      linarith
    · have h1 := Wf_mono μ f' f hμ hf'.1 h
      have h2 := Wf_lip μ f' f hμ hf'.1 h
      rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
      linarith
  have hin : ContinuousOn (fun η : ℝ => 1 - 1 / η) (Ici 1) := by
    apply ContinuousOn.sub continuousOn_const
    apply ContinuousOn.div continuousOn_const continuousOn_id
    intro x hx; exact ne_of_gt (lt_of_lt_of_le one_pos hx)
  have hmaps : MapsTo (fun η : ℝ => 1 - 1 / η) (Ici 1) (Icc 0 1) := by
    intro η hη
    have hη0 : 0 < η := lt_of_lt_of_le one_pos hη
    constructor
    · rw [sub_nonneg, div_le_one hη0]; exact hη
    · have : 0 < 1 / η := by positivity
      linarith
  have hcomp := hWlip.continuousOn.comp hin hmaps
  have : calibratedPenalty μ = fun η => η * (1 + Wf μ (1 - 1 / η)) := by
    funext η; rfl
  rw [this]
  exact continuousOn_id.mul (continuousOn_const.add hcomp)

lemma calibratedPenalty_strictMonoOn (μ : ℝ) (hμ : 0 ≤ μ) :
    StrictMonoOn (calibratedPenalty μ) (Ici 1) := by
  intro η hη η' hη' hlt
  have hη0 : 0 < η := lt_of_lt_of_le one_pos hη
  have hη'0 : 0 < η' := lt_of_lt_of_le one_pos hη'
  have hf0 : 0 ≤ 1 - 1 / η := by rw [sub_nonneg, div_le_one hη0]; exact hη
  have hff : 1 - 1 / η ≤ 1 - 1 / η' := by
    have : 1 / η' ≤ 1 / η := one_div_le_one_div_of_le hη0 hlt.le
    linarith
  have hW := Wf_mono μ _ _ hμ hf0 hff
  have hWnn := Wf_nonneg μ _ hμ (hf0.trans hff)
  rw [calibratedPenalty_eq, calibratedPenalty_eq]
  nlinarith

lemma calibratedPenalty_bijOn (μ : ℝ) (hμ : 0 ≤ μ) :
    BijOn (calibratedPenalty μ) (Ici 1) (Ici 1) := by
  have hge : ∀ η ∈ Ici (1:ℝ), η ≤ calibratedPenalty μ η := by
    intro η hη
    have hη0 : 0 < η := lt_of_lt_of_le one_pos hη
    have hf0 : 0 ≤ 1 - 1 / η := by rw [sub_nonneg, div_le_one hη0]; exact hη
    have := Wf_nonneg μ _ hμ hf0
    rw [calibratedPenalty_eq]
    nlinarith
  refine ⟨fun η hη => le_trans hη (hge η hη), (calibratedPenalty_strictMonoOn μ hμ).injOn, ?_⟩
  intro y hy
  have hy1 : (1:ℝ) ≤ y := hy
  have h1 : calibratedPenalty μ 1 = 1 := by
    rw [calibratedPenalty_eq]; norm_num [Wf_zero μ hμ]
  have hyy := hge y hy
  have hmem : y ∈ Icc (calibratedPenalty μ 1) (calibratedPenalty μ y) := ⟨by rw [h1]; exact hy1, hyy⟩
  obtain ⟨η, hη, hηy⟩ := intermediate_value_Icc hy1
    ((calibratedPenalty_continuousOn μ hμ).mono Icc_subset_Ici_self) hmem
  exact ⟨η, hη.1, hηy⟩

end LostSalesRQ


namespace LostSalesRQ

open MeasureTheory Set Real

lemma g_pdf_pos (z : ℝ) : 0 < stdNormalPdf z := by unfold stdNormalPdf; positivity

lemma g_pdf_eq (z : ℝ) : stdNormalPdf z = ProbabilityTheory.gaussianPDFReal 0 1 z := by
  unfold stdNormalPdf
  rw [ProbabilityTheory.gaussianPDFReal]
  simp only [NNReal.coe_one, mul_one, sub_zero]
  rw [div_eq_inv_mul]

lemma g_pdf_int : Integrable stdNormalPdf := by
  have : stdNormalPdf = ProbabilityTheory.gaussianPDFReal 0 1 := funext g_pdf_eq
  rw [this]; exact ProbabilityTheory.integrable_gaussianPDFReal 0 1

lemma g_pdf_integral : ∫ x, stdNormalPdf x = 1 := by
  have : stdNormalPdf = ProbabilityTheory.gaussianPDFReal 0 1 := funext g_pdf_eq
  rw [this]; exact ProbabilityTheory.integral_gaussianPDFReal_eq_one 0 one_ne_zero

lemma g_pdf_cont : Continuous stdNormalPdf := by
  unfold stdNormalPdf; fun_prop

lemma g_pdf_neg (z : ℝ) : stdNormalPdf (-z) = stdNormalPdf z := by
  unfold stdNormalPdf; rw [neg_sq]

lemma g_pdf_deriv (z : ℝ) : HasDerivAt stdNormalPdf (-z * stdNormalPdf z) z := by
  unfold stdNormalPdf
  have h1 : HasDerivAt (fun x : ℝ => -(x ^ 2) / 2) (-z) z := by
    have h := ((hasDerivAt_pow 2 z).neg).div_const 2
    have e : -((2 : ℕ) * z ^ (2 - 1)) / 2 = -z := by push_cast; ring
    rw [e] at h
    exact h
  have h2 := (h1.exp).div_const (Real.sqrt (2 * Real.pi))
  exact h2.congr_deriv (by ring)

lemma g_cdf_eq (z : ℝ) :
    stdNormalCdf z = stdNormalCdf 0 + ∫ x in (0 : ℝ)..z, stdNormalPdf x := by
  unfold stdNormalCdf
  have := intervalIntegral.integral_Iic_sub_Iic (f := stdNormalPdf) (μ := volume) (a := 0) (b := z)
    g_pdf_int.integrableOn g_pdf_int.integrableOn
  linarith

lemma g_cdf_deriv (z : ℝ) : HasDerivAt stdNormalCdf (stdNormalPdf z) z := by
  have hfun : stdNormalCdf = fun z => stdNormalCdf 0 + ∫ x in (0 : ℝ)..z, stdNormalPdf x :=
    funext g_cdf_eq
  rw [hfun]
  apply HasDerivAt.const_add
  exact intervalIntegral.integral_hasDerivAt_right (g_pdf_int.intervalIntegrable)
    (g_pdf_cont.stronglyMeasurableAtFilter _ _) g_pdf_cont.continuousAt

lemma g_cdf_tail (z : ℝ) : stdNormalCdf z + ∫ x in Ioi z, stdNormalPdf x = 1 := by
  unfold stdNormalCdf
  rw [intervalIntegral.integral_Iic_add_Ioi g_pdf_int.integrableOn g_pdf_int.integrableOn]
  exact g_pdf_integral

/-- Translation of an integral over a half line. -/
lemma g_shift (g : ℝ → ℝ) (z : ℝ) :
    ∫ x in Ioi z, g x = ∫ t in Ioi 0, g (t + z) := by
  rw [← integral_indicator measurableSet_Ioi, ← integral_indicator measurableSet_Ioi]
  rw [← integral_add_right_eq_self (μ := volume) ((Ioi z).indicator g) z]
  congr 1
  ext t
  simp only [Set.indicator, Set.mem_Ioi]
  by_cases h : 0 < t
  · rw [if_pos h, if_pos (by linarith)]
  · rw [if_neg h, if_neg (by linarith)]

/-- The Mills-type integral. -/
noncomputable def gI (z : ℝ) : ℝ := ∫ t in Ioi 0, Real.exp (z * t - t ^ 2 / 2)

lemma g_exp_int (z : ℝ) : Integrable (fun t : ℝ => Real.exp (z * t - t ^ 2 / 2)) := by
  have e : (fun t : ℝ => Real.exp (z * t - t ^ 2 / 2)) =
      fun t => Real.exp (z ^ 2 / 2) * Real.exp (-(1 / 2 : ℝ) * (t - z) ^ 2) := by
    ext t; rw [← Real.exp_add]; ring_nf
  rw [e]
  exact ((integrable_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1 / 2)).comp_sub_right z).const_mul _

lemma g_tail_rep (z : ℝ) :
    ∫ x in Ioi z, stdNormalPdf x = stdNormalPdf z * gI (-z) := by
  rw [g_shift, gI, ← integral_const_mul]
  congr 1
  ext t
  unfold stdNormalPdf
  rw [div_mul_eq_mul_div, ← Real.exp_add]
  congr 2
  ring

lemma g_cdf_rep (z : ℝ) : stdNormalCdf z = stdNormalPdf z * gI z := by
  have h1 : stdNormalCdf z = ∫ y in Ioi (-z), stdNormalPdf y := by
    unfold stdNormalCdf
    have h := integral_comp_neg_Ioi (-z) stdNormalPdf
    rw [neg_neg] at h
    rw [← h]
    congr 1
    ext y
    rw [g_pdf_neg]
  rw [h1, g_tail_rep, neg_neg, g_pdf_neg]

lemma g_I_pos (z : ℝ) : 0 < gI z := by
  unfold gI
  rw [setIntegral_pos_iff_support_of_nonneg_ae]
  · have : Function.support (fun t : ℝ => Real.exp (z * t - t ^ 2 / 2)) = univ := by
      ext t; simp [(Real.exp_pos _).ne']
    rw [this, univ_inter, Real.volume_Ioi]
    simp
  · exact Filter.Eventually.of_forall (fun t => (Real.exp_pos _).le)
  · exact (g_exp_int z).integrableOn

lemma g_cdf_pos (z : ℝ) : 0 < stdNormalCdf z := by
  rw [g_cdf_rep]; exact mul_pos (g_pdf_pos z) (g_I_pos z)

lemma g_cdf_lt_one (z : ℝ) : stdNormalCdf z < 1 := by
  have h := g_cdf_tail z
  rw [g_tail_rep] at h
  have := mul_pos (g_pdf_pos z) (g_I_pos (-z))
  linarith

end LostSalesRQ

namespace LostSalesRQ

open MeasureTheory Set Real

lemma g_moment_int {x : ℝ} (hx : 0 < x) (n : ℕ) :
    IntegrableOn (fun t : ℝ => t ^ n * Real.exp (-x * t)) (Ioi 0) := by
  have h := integrableOn_rpow_mul_exp_neg_mul_rpow (s := (n : ℝ)) (p := 1) (b := x)
    (by have := Nat.cast_nonneg (α := ℝ) n; linarith) one_pos hx
  refine h.congr_fun (fun t ht => ?_) measurableSet_Ioi
  simp only [Real.rpow_natCast, Real.rpow_one]

lemma g_moment {x : ℝ} (hx : 0 < x) (n : ℕ) :
    ∫ t in Ioi 0, t ^ n * Real.exp (-x * t) = (n.factorial : ℝ) / x ^ (n + 1) := by
  have h := integral_rpow_mul_exp_neg_mul_rpow (p := 1) (q := (n : ℝ)) (b := x) one_pos
    (by have := Nat.cast_nonneg (α := ℝ) n; linarith) hx
  have e1 : ∫ t in Ioi 0, t ^ n * Real.exp (-x * t) =
      ∫ t in Ioi 0, t ^ (n : ℝ) * Real.exp (-x * t ^ (1 : ℝ)) := by
    refine setIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
    simp only [Real.rpow_natCast, Real.rpow_one]
  rw [e1, h]
  simp only [div_one, one_div, inv_one, mul_one]
  rw [Real.Gamma_nat_eq_factorial, Real.rpow_neg hx.le]
  rw [show ((n : ℝ) + 1) = ((n + 1 : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast]
  rw [div_eq_inv_mul]

lemma g_exp_quad {y : ℝ} (hy : 0 ≤ y) : Real.exp (-y) ≤ 1 - y + y ^ 2 / 2 := by
  have h4 := Real.sum_le_exp_of_nonneg hy 4
  simp [Finset.sum_range_succ, Nat.factorial] at h4
  have hpos : 0 < 1 + y + y ^ 2 / 2 + y ^ 3 / 6 := by positivity
  have hprod : Real.exp (-y) * Real.exp y = 1 := by rw [← Real.exp_add]; simp
  have hle : Real.exp (-y) * (1 + y + y ^ 2 / 2 + y ^ 3 / 6) ≤ 1 := by
    have := mul_le_mul_of_nonneg_left (by linarith : 1 + y + y ^ 2 / 2 + y ^ 3 / 6 ≤ Real.exp y)
      (Real.exp_pos (-y)).le
    linarith
  have hpoly : 1 ≤ (1 - y + y ^ 2 / 2) * (1 + y + y ^ 2 / 2 + y ^ 3 / 6) := by
    nlinarith [pow_nonneg hy 3, pow_nonneg hy 4, pow_nonneg hy 5]
  by_contra hcon
  push Not at hcon
  have := mul_lt_mul_of_pos_right hcon hpos
  linarith

lemma g_I_neg_eq (x : ℝ) : gI (-x) = ∫ t in Ioi 0, Real.exp (-x * t) * Real.exp (-(t ^ 2) / 2) := by
  unfold gI
  congr 1; ext t
  rw [← Real.exp_add]; ring_nf

lemma g_I_neg_lt {x : ℝ} (hx : 0 < x) : gI (-x) < 1 / x := by
  have h1 : ∫ t in Ioi 0, Real.exp (-x * t) = 1 / x := by
    rw [integral_exp_mul_Ioi (by linarith : -x < 0) 0]; simp
  have hint1 : IntegrableOn (fun t : ℝ => Real.exp (-x * t)) (Ioi 0) :=
    integrableOn_exp_mul_Ioi (by linarith) 0
  have hint2 : IntegrableOn (fun t : ℝ => Real.exp (-x * t) * Real.exp (-(t ^ 2) / 2)) (Ioi 0) := by
    have := (g_exp_int (-x)).integrableOn (s := Ioi 0)
    refine this.congr_fun (fun t _ => ?_) measurableSet_Ioi
    rw [← Real.exp_add]; ring_nf
  have hpos : 0 < ∫ t in Ioi 0, (Real.exp (-x * t) - Real.exp (-x * t) * Real.exp (-(t ^ 2) / 2)) := by
    rw [setIntegral_pos_iff_support_of_nonneg_ae]
    · have hsub : Ioi (0 : ℝ) ⊆ Function.support
          (fun t : ℝ => Real.exp (-x * t) - Real.exp (-x * t) * Real.exp (-(t ^ 2) / 2)) ∩ Ioi 0 := by
        intro t ht
        refine ⟨?_, ht⟩
        have ht' : (0 : ℝ) < t := ht
        have hlt : Real.exp (-(t ^ 2) / 2) < 1 := by
          rw [Real.exp_lt_one_iff]; nlinarith
        have he := Real.exp_pos (-x * t)
        simp only [Function.mem_support]
        nlinarith
      have := measure_mono (μ := volume) hsub
      rw [Real.volume_Ioi] at this
      exact lt_of_lt_of_le (by simp) this
    · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall (fun t ht => ?_))
      have hle : Real.exp (-(t ^ 2) / 2) ≤ 1 := by rw [Real.exp_le_one_iff]; nlinarith
      have he := Real.exp_pos (-x * t)
      simp only [Pi.zero_apply]
      nlinarith
    · exact hint1.sub hint2
  rw [integral_sub hint1 hint2, h1, ← g_I_neg_eq] at hpos
  linarith

lemma g_I_neg_le {x : ℝ} (hx : 0 < x) : gI (-x) ≤ 1 / x - 1 / x ^ 3 + 3 / x ^ 5 := by
  have m0 := g_moment hx 0
  have m2 := g_moment hx 2
  have m4 := g_moment hx 4
  simp only [pow_zero, one_mul, Nat.factorial, Nat.succ_eq_add_one, zero_add] at m0 m2 m4
  have i0 := g_moment_int hx 0
  have i2 := g_moment_int hx 2
  have i4 := g_moment_int hx 4
  simp only [pow_zero, one_mul] at i0
  have hint2 : IntegrableOn (fun t : ℝ => Real.exp (-x * t) * Real.exp (-(t ^ 2) / 2)) (Ioi 0) := by
    have := (g_exp_int (-x)).integrableOn (s := Ioi 0)
    refine this.congr_fun (fun t _ => ?_) measurableSet_Ioi
    rw [← Real.exp_add]; ring_nf
  have hcomb : IntegrableOn (fun t : ℝ => Real.exp (-x * t) - (1 / 2) * (t ^ 2 * Real.exp (-x * t)) +
      (1 / 8) * (t ^ 4 * Real.exp (-x * t))) (Ioi 0) :=
    (i0.sub (i2.const_mul (1 / 2))).add (i4.const_mul (1 / 8))
  have hmono : ∫ t in Ioi 0, Real.exp (-x * t) * Real.exp (-(t ^ 2) / 2) ≤
      ∫ t in Ioi 0, (Real.exp (-x * t) - (1 / 2) * (t ^ 2 * Real.exp (-x * t)) +
        (1 / 8) * (t ^ 4 * Real.exp (-x * t))) := by
    apply setIntegral_mono_on hint2 hcomb measurableSet_Ioi
    intro t _
    have hq := g_exp_quad (by positivity : (0 : ℝ) ≤ t ^ 2 / 2)
    have e : Real.exp (-(t ^ 2) / 2) = Real.exp (-(t ^ 2 / 2)) := by ring_nf
    rw [e]
    have he := Real.exp_pos (-x * t)
    have := mul_le_mul_of_nonneg_left hq he.le
    nlinarith
  have hsplit : ∫ t in Ioi 0, (Real.exp (-x * t) - (1 / 2) * (t ^ 2 * Real.exp (-x * t)) +
      (1 / 8) * (t ^ 4 * Real.exp (-x * t))) =
      (∫ t in Ioi 0, Real.exp (-x * t)) - (1 / 2) * (∫ t in Ioi 0, t ^ 2 * Real.exp (-x * t)) +
        (1 / 8) * (∫ t in Ioi 0, t ^ 4 * Real.exp (-x * t)) := by
    rw [integral_add, integral_sub, integral_const_mul, integral_const_mul]
    · exact i0
    · exact i2.const_mul _
    · exact i0.sub (i2.const_mul _)
    · exact i4.const_mul _
  rw [hsplit, m0, m2, m4, ← g_I_neg_eq] at hmono
  have e : (1 : ℝ) / x ^ 1 - 1 / 2 * (((1 + 1) * 1 : ℕ) / x ^ 3) +
      1 / 8 * ((((3 + 1) * ((2 + 1) * ((1 + 1) * 1))) : ℕ) / x ^ 5) = 1 / x - 1 / x ^ 3 + 3 / x ^ 5 := by
    push_cast; field_simp; ring
  linarith [hmono, e]

lemma g_I_cs (z : ℝ) : Real.pi / 2 ≤ gI z * gI (-z) := by
  have ha := g_I_pos z
  have hb := g_I_pos (-z)
  set a := gI z with hadef
  set b := gI (-z) with hbdef
  set l := Real.sqrt (b / a) with hl
  have hl0 : 0 < l := Real.sqrt_pos.mpr (div_pos hb ha)
  have hl2 : l ^ 2 = b / a := Real.sq_sqrt (div_pos hb ha).le
  have hg : ∫ t in Ioi 0, Real.exp (-(1 / 2 : ℝ) * t ^ 2) = Real.sqrt (Real.pi / (1 / 2)) / 2 :=
    integral_gaussian_Ioi (1 / 2)
  have hgint : IntegrableOn (fun t : ℝ => Real.exp (-(1 / 2 : ℝ) * t ^ 2)) (Ioi 0) :=
    (integrable_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1 / 2)).integrableOn
  have hint : IntegrableOn (fun t : ℝ => (l * Real.exp (z * t - t ^ 2 / 2) +
      l⁻¹ * Real.exp (-z * t - t ^ 2 / 2)) / 2) (Ioi 0) :=
    ((((g_exp_int z).integrableOn).const_mul l).add
      (((g_exp_int (-z)).integrableOn).const_mul l⁻¹)).div_const 2
  have hmono : ∫ t in Ioi 0, Real.exp (-(1 / 2 : ℝ) * t ^ 2) ≤
      ∫ t in Ioi 0, (l * Real.exp (z * t - t ^ 2 / 2) + l⁻¹ * Real.exp (-z * t - t ^ 2 / 2)) / 2 := by
    apply setIntegral_mono_on hgint hint measurableSet_Ioi
    intro t _
    have e1 : Real.exp (z * t - t ^ 2 / 2) = Real.exp (z * t) * Real.exp (-(1 / 2 : ℝ) * t ^ 2) := by
      rw [← Real.exp_add]; ring_nf
    have e2 : Real.exp (-z * t - t ^ 2 / 2) = (Real.exp (z * t))⁻¹ * Real.exp (-(1 / 2 : ℝ) * t ^ 2) := by
      rw [← Real.exp_neg, ← Real.exp_add]; ring_nf
    rw [e1, e2]
    set c := l * Real.exp (z * t) with hc
    have hc0 : 0 < c := mul_pos hl0 (Real.exp_pos _)
    have hE := Real.exp_pos (-(1 / 2 : ℝ) * t ^ 2)
    have key : l⁻¹ * ((Real.exp (z * t))⁻¹) = c⁻¹ := by rw [hc, mul_inv]
    have hamgm : 2 ≤ c + c⁻¹ := by
      have := sq_nonneg (c - 1)
      have : c + c⁻¹ - 2 = (c - 1) ^ 2 / c := by field_simp; ring
      have : 0 ≤ (c - 1) ^ 2 / c := div_nonneg (sq_nonneg _) hc0.le
      linarith
    have e3 : (l * (Real.exp (z * t) * Real.exp (-(1 / 2 : ℝ) * t ^ 2)) +
        l⁻¹ * ((Real.exp (z * t))⁻¹ * Real.exp (-(1 / 2 : ℝ) * t ^ 2))) / 2 =
        (c + c⁻¹) / 2 * Real.exp (-(1 / 2 : ℝ) * t ^ 2) := by
      rw [← key, hc]; ring
    rw [e3]
    nlinarith
  rw [integral_div, integral_add (((g_exp_int z).integrableOn).const_mul l)
    (((g_exp_int (-z)).integrableOn).const_mul l⁻¹), integral_const_mul, integral_const_mul, hg] at hmono
  have hIz : ∫ t in Ioi 0, Real.exp (z * t - t ^ 2 / 2) = a := rfl
  have hInz : ∫ t in Ioi 0, Real.exp (-z * t - t ^ 2 / 2) = b := rfl
  rw [hIz, hInz] at hmono
  -- l * a + l⁻¹ * b = 2 * sqrt (a b)
  have hlab : l * a = l⁻¹ * b := by
    have : l * l * a = b := by rw [← sq, hl2]; field_simp
    field_simp; linarith
  have hs : Real.sqrt (Real.pi / (1 / 2)) / 2 ≤ l * a := by linarith
  have hs2 : (Real.sqrt (Real.pi / (1 / 2)) / 2) ^ 2 = Real.pi / 2 := by
    rw [div_pow, Real.sq_sqrt (by positivity)]; ring
  have hla2 : (l * a) ^ 2 = a * b := by rw [mul_pow, hl2]; field_simp
  have h0 : 0 ≤ Real.sqrt (Real.pi / (1 / 2)) / 2 := by positivity
  nlinarith [mul_le_mul hs hs h0 (by positivity : 0 ≤ l * a)]

end LostSalesRQ

namespace LostSalesRQ

open MeasureTheory Set Real Filter Topology

noncomputable def gU (z : ℝ) : ℝ := stdNormalCdf z / stdNormalPdf z

lemma gU_eq (z : ℝ) : gU z = gI z := by
  unfold gU; rw [g_cdf_rep]; field_simp [(g_pdf_pos z).ne']

lemma gU_pos (z : ℝ) : 0 < gU z := by rw [gU_eq]; exact g_I_pos z

lemma gU_deriv (z : ℝ) : HasDerivAt gU (1 + z * gU z) z := by
  have h := (g_cdf_deriv z).div (g_pdf_deriv z) (g_pdf_pos z).ne'
  unfold gU
  refine h.congr_deriv ?_
  have := (g_pdf_pos z).ne'
  field_simp
  ring

lemma gU_cont : Continuous gU :=
  continuous_iff_continuousAt.mpr (fun z => (gU_deriv z).continuousAt)

lemma g_one_add (z : ℝ) : 0 < 1 + z * gU z := by
  rcases le_or_gt 0 z with hz | hz
  · have := gU_pos z; nlinarith
  · have hx : 0 < -z := by linarith
    have h := g_I_neg_lt hx
    rw [neg_neg] at h
    rw [gU_eq]
    have : (-z) * gI z < 1 := by
      have := mul_lt_mul_of_pos_left h hx
      rw [mul_one_div_cancel hx.ne'] at this
      exact this
    linarith

lemma gU_strictMono : StrictMono gU := by
  apply strictMono_of_deriv_pos
  intro x
  rw [(gU_deriv x).deriv]
  exact g_one_add x

lemma gU_ge (z : ℝ) (hz : 0 ≤ z) : z < gU z := by
  have hmono : MonotoneOn (fun y => gU y - y) (Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
    · exact (gU_cont.sub continuous_id).continuousOn
    · intro y _
      have hd : HasDerivAt (fun y => gU y - y) (1 + y * gU y - 1) y :=
        (gU_deriv y).sub (hasDerivAt_id' y)
      exact hd.differentiableAt.differentiableWithinAt
    · intro y hy
      rw [interior_Ici] at hy
      have hy' : 0 < y := hy
      have hd : HasDerivAt (fun y => gU y - y) (1 + y * gU y - 1) y :=
        (gU_deriv y).sub (hasDerivAt_id' y)
      rw [hd.deriv]
      have := gU_pos y
      nlinarith
  have := hmono (mem_Ici.mpr le_rfl) (mem_Ici.mpr hz) hz
  simp only at this
  have h0 := gU_pos 0
  linarith

lemma gU_surj {s : ℝ} (hs : 0 < s) : ∃ z, gU z = s := by
  have h1 : gU (-(2 / s)) < s := by
    have hx : 0 < 2 / s := by positivity
    have h := g_I_neg_lt hx
    rw [gU_eq]
    have : 1 / (2 / s) = s / 2 := by field_simp
    rw [this] at h
    linarith
  have h2 : s < gU (s + 1) := by
    have := gU_ge (s + 1) (by linarith)
    linarith
  have hle : -(2 / s) ≤ s + 1 := by
    have : 0 < 2 / s := by positivity
    linarith
  obtain ⟨z, _, hz⟩ := intermediate_value_Icc hle gU_cont.continuousOn ⟨h1.le, h2.le⟩
  exact ⟨z, hz⟩

/-- The crossing lemma (positivity propagates from the right). -/
lemma g2_crossing (f : ℝ → ℝ) (a : ℝ)
    (hd : ∀ t, a ≤ t → ∃ d, HasDerivAt f d t ∧ (f t = 0 → d < 0))
    (hlarge : ∀ M, ∃ t, M ≤ t ∧ 0 < f t) : ∀ t, a ≤ t → 0 < f t := by
  intro t0 ht0
  by_contra hneg
  push Not at hneg
  obtain ⟨t1, ht1, hf1⟩ := hlarge (t0 + 1)
  have hcont : ∀ t, a ≤ t → ContinuousAt f t := fun t ht => by
    obtain ⟨d, hdt, _⟩ := hd t ht; exact hdt.continuousAt
  have hcontOn : ContinuousOn f (Set.Icc t0 t1) := fun t ht =>
    (hcont t (le_trans ht0 ht.1)).continuousWithinAt
  set S := Set.Icc t0 t1 ∩ f ⁻¹' Set.Iic 0 with hS
  have hSc : IsClosed S := hcontOn.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Iic
  have hSne : S.Nonempty := ⟨t0, ⟨le_refl _, by linarith⟩, hneg⟩
  have hSb : BddAbove S := ⟨t1, fun t ht => ht.1.2⟩
  have hsS : sSup S ∈ S := hSc.csSup_mem hSne hSb
  set s := sSup S with hsdef
  have hfs : f s ≤ 0 := hsS.2
  have hst1 : s < t1 := by
    rcases lt_or_eq_of_le hsS.1.2 with h | h
    · exact h
    · exfalso; rw [h] at hfs; linarith
  have hpos : ∀ t, s < t → t ≤ t1 → 0 < f t := by
    intro t hst htt1
    by_contra hc
    push Not at hc
    have hmem : t ∈ S := ⟨⟨by linarith [hsS.1.1], htt1⟩, hc⟩
    have := le_csSup hSb hmem
    linarith
  have has : a ≤ s := le_trans ht0 hsS.1.1
  have hfs0 : f s = 0 := by
    by_contra hne
    have hlt : f s < 0 := lt_of_le_of_ne hfs hne
    have hev : ∀ᶠ y in 𝓝 s, f y < 0 := (hcont s has).eventually (Iio_mem_nhds hlt)
    have hev2 : ∀ᶠ y in 𝓝[>] s, f y < 0 ∧ y ∈ Set.Ioo s t1 :=
      (hev.filter_mono nhdsWithin_le_nhds).and (Ioo_mem_nhdsGT hst1)
    obtain ⟨y, hy1, hy2⟩ := hev2.exists
    linarith [hpos y hy2.1 hy2.2.le]
  obtain ⟨d, hdd, hdneg⟩ := hd s has
  have hd0 := hdneg hfs0
  have hslope := hasDerivAt_iff_tendsto_slope.mp hdd
  have hev : ∀ᶠ y in 𝓝[≠] s, slope f s y < 0 := hslope.eventually (Iio_mem_nhds hd0)
  have hev' : ∀ᶠ y in 𝓝[>] s, slope f s y < 0 :=
    hev.filter_mono (nhdsWithin_mono s fun y hy => Set.mem_compl_singleton_iff.mpr (ne_of_gt hy))
  obtain ⟨y, hy1, hy2⟩ := (hev'.and (Ioo_mem_nhdsGT hst1)).exists
  rw [slope_def_field, hfs0] at hy1
  have hys : 0 < y - s := by linarith [hy2.1]
  have hfy : f y - 0 < 0 := by
    by_contra hc
    push Not at hc
    have := div_nonneg hc hys.le
    linarith
  linarith [hpos y hy2.1 hy2.2.le]

/-- The polynomial F(z,u) = 2 z u^3 - 8 u^2 + 13 z u + 13 (four times u^2 (S - 4)/2). -/
def gF (z u : ℝ) : ℝ := 2 * z * u ^ 3 - 8 * u ^ 2 + 13 * z * u + 13

lemma gF_cross {z u : ℝ} (hu : 0 < u) (hf : gF z u = 0) :
    0 < 6 * u ^ 3 * z ^ 2 + 2 * u ^ 3 - 10 * u ^ 2 * z + 13 * u * z ^ 2 - 3 * u + 13 * z := by
  unfold gF at hf
  have hP : 0 < 8 * (u ^ 2) ^ 3 + 316 * (u ^ 2) ^ 2 - 806 * u ^ 2 + 507 := by
    have hw : 0 ≤ u ^ 2 := sq_nonneg u
    nlinarith [sq_nonneg (u ^ 2 - 5/4), mul_nonneg hw (sq_nonneg (u ^ 2 - 5/4)),
      sq_nonneg (u ^ 2 - 6/5), mul_nonneg hw (sq_nonneg (u ^ 2 - 6/5))]
  have key : (6 * u ^ 3 * z ^ 2 + 2 * u ^ 3 - 10 * u ^ 2 * z + 13 * u * z ^ 2 - 3 * u + 13 * z) *
      (2 * u ^ 2 + 13) ^ 2 = u * (8 * (u ^ 2) ^ 3 + 316 * (u ^ 2) ^ 2 - 806 * u ^ 2 + 507) := by
    linear_combination (12 * u ^ 4 * z + 28 * u ^ 3 + 104 * u ^ 2 * z - 78 * u + 169 * z) * hf
  have h2 : 0 < (2 * u ^ 2 + 13) ^ 2 := by positivity
  have h3 : 0 < u * (8 * (u ^ 2) ^ 3 + 316 * (u ^ 2) ^ 2 - 806 * u ^ 2 + 507) := mul_pos hu hP
  rw [← key] at h3
  exact pos_of_mul_pos_left h3 h2.le

lemma g_N_pos {x : ℝ} (hx : 4 ≤ x) :
    0 < 3 * x ^ 12 - 17 * x ^ 10 - 80 * x ^ 8 + 86 * x ^ 6 - 144 * x ^ 4 + 54 * x ^ 2 - 54 := by
  have hw : 16 ≤ x ^ 2 := by nlinarith
  set w := x ^ 2 with hwdef
  have e : 3 * x ^ 12 - 17 * x ^ 10 - 80 * x ^ 8 + 86 * x ^ 6 - 144 * x ^ 4 + 54 * x ^ 2 - 54 =
      3 * w ^ 6 - 17 * w ^ 5 - 80 * w ^ 4 + 86 * w ^ 3 - 144 * w ^ 2 + 54 * w - 54 := by
    rw [hwdef]; ring
  rw [e]
  have h1 : 0 < w ^ 4 * (3 * w ^ 2 - 17 * w - 80) := by
    have : 0 < 3 * w ^ 2 - 17 * w - 80 := by nlinarith
    positivity
  have h2 : 0 < w ^ 2 * (86 * w - 144) + 54 * (w - 1) := by
    have : 0 < 86 * w - 144 := by linarith
    have : 0 < w ^ 2 := by positivity
    nlinarith
  nlinarith

lemma gF_far {z : ℝ} (hz : z ≤ -4) : 0 < gF z (gU z) := by
  set x := -z with hxdef
  have hx : 4 ≤ x := by linarith
  have hx0 : 0 < x := by linarith
  have hu0 := gU_pos z
  have hle : gU z ≤ 1 / x - 1 / x ^ 3 + 3 / x ^ 5 := by
    have h := g_I_neg_le hx0
    rw [hxdef, neg_neg, ← gU_eq] at h
    exact h
  set u := gU z
  set U := 1 / x - 1 / x ^ 3 + 3 / x ^ 5 with hU
  have hzx : z = -x := by rw [hxdef]; ring
  unfold gF
  rw [hzx]
  have h1 : u ^ 2 ≤ U ^ 2 := pow_le_pow_left₀ hu0.le hle 2
  have h2 : u ^ 3 ≤ U ^ 3 := pow_le_pow_left₀ hu0.le hle 3
  have hbase : 0 < 13 - 13 * x * U - 8 * U ^ 2 - 2 * x * U ^ 3 := by
    have e : (13 - 13 * x * U - 8 * U ^ 2 - 2 * x * U ^ 3) * x ^ 14 =
        3 * x ^ 12 - 17 * x ^ 10 - 80 * x ^ 8 + 86 * x ^ 6 - 144 * x ^ 4 + 54 * x ^ 2 - 54 := by
      rw [hU]; field_simp; ring
    have hN := g_N_pos hx
    rw [← e] at hN
    exact pos_of_mul_pos_left hN (by positivity)
  have i1 := mul_le_mul_of_nonneg_left hle (by linarith : (0 : ℝ) ≤ 13 * x)
  have i2 := mul_le_mul_of_nonneg_left h2 (by linarith : (0 : ℝ) ≤ 2 * x)
  nlinarith

lemma gF_pos (z : ℝ) : 0 < gF z (gU z) := by
  -- apply the crossing lemma to t ↦ F(-t, u(-t))
  set g : ℝ → ℝ := fun t => gF (-t) (gU (-t)) with hg
  have hd : ∀ t, (-z) ≤ t → ∃ d, HasDerivAt g d t ∧ (g t = 0 → d < 0) := by
    intro t _
    have hu := (gU_deriv (-t)).comp t (hasDerivAt_neg t)
    have hz : HasDerivAt (fun t : ℝ => -t) (-1) t := hasDerivAt_neg t
    set u := gU (-t)
    have hG : HasDerivAt g (-(6 * u ^ 3 * (-t) ^ 2 + 2 * u ^ 3 - 10 * u ^ 2 * (-t) +
        13 * u * (-t) ^ 2 - 3 * u + 13 * (-t))) t := by
      have h := ((((hz.const_mul 2).mul (hu.pow 3)).sub ((hu.pow 2).const_mul 8)).add
        ((hz.const_mul 13).mul hu)).add_const 13
      refine h.congr_deriv ?_
      simp only [Function.comp, Pi.pow_apply, Nat.cast_ofNat]
      ring
    refine ⟨_, hG, fun h0 => ?_⟩
    have := gF_cross (gU_pos (-t)) h0
    linarith
  have hlarge : ∀ M, ∃ t, M ≤ t ∧ 0 < g t := by
    intro M
    refine ⟨max M 4, le_max_left _ _, ?_⟩
    exact gF_far (by have := le_max_right M 4; linarith)
  have := g2_crossing g (-z) hd hlarge (-z) le_rfl
  simpa [hg] using this

lemma g_tail_eq (z : ℝ) : 1 - stdNormalCdf z = stdNormalPdf z * gI (-z) := by
  have h := g_cdf_tail z
  rw [g_tail_rep] at h
  linarith

lemma g_K_pos (z : ℝ) :
    0 < 13 + 13 * z * gU z - 11 * gU z ^ 2 + 2 * z * gU z ^ 3 + 2 * gU z ^ 3 * gI (-z) := by
  have hF := gF_pos z
  unfold gF at hF
  have hcs := g_I_cs z
  rw [← gU_eq] at hcs
  have hu := gU_pos z
  have hpi : (3 : ℝ) < Real.pi := Real.pi_gt_three
  have h1 : 3 / 2 < gU z * gI (-z) := by linarith
  have h2 : 0 < gU z ^ 2 * (2 * (gU z * gI (-z)) - 3) := by
    have : 0 < 2 * (gU z * gI (-z)) - 3 := by linarith
    positivity
  nlinarith

end LostSalesRQ

namespace LostSalesRQ

open MeasureTheory ProbabilityTheory Filter Set Topology

noncomputable def bu (ℓ τ y : ℝ) : ℝ := y / Real.sqrt τ + ℓ * Real.sqrt τ
noncomputable def bv (ℓ τ y : ℝ) : ℝ := ℓ * Real.sqrt τ - y / Real.sqrt τ

/-- Expected excess over y of the maximum on [0,τ] of a Brownian motion with drift -ℓ. -/
noncomputable def BV (ℓ τ y : ℝ) : ℝ :=
  Real.sqrt τ * stdNormalPdf (bu ℓ τ y) - (y + ℓ * τ) * (1 - stdNormalCdf (bu ℓ τ y)) +
    (Real.exp (-(2 * ℓ * y)) * stdNormalCdf (bv ℓ τ y) - (1 - stdNormalCdf (bu ℓ τ y))) / (2 * ℓ)

noncomputable def BVy (ℓ τ y : ℝ) : ℝ :=
  -(1 - stdNormalCdf (bu ℓ τ y)) - Real.exp (-(2 * ℓ * y)) * stdNormalCdf (bv ℓ τ y)

noncomputable def BVyy (ℓ τ y : ℝ) : ℝ :=
  2 * stdNormalPdf (bu ℓ τ y) / Real.sqrt τ +
    2 * ℓ * (Real.exp (-(2 * ℓ * y)) * stdNormalCdf (bv ℓ τ y))

noncomputable def BVt (ℓ τ y : ℝ) : ℝ :=
  stdNormalPdf (bu ℓ τ y) / Real.sqrt τ - ℓ * (1 - stdNormalCdf (bu ℓ τ y))

lemma b_pdf_id (ℓ τ y : ℝ) (hτ : 0 < τ) :
    Real.exp (-(2 * ℓ * y)) * stdNormalPdf (bv ℓ τ y) = stdNormalPdf (bu ℓ τ y) := by
  have hs : 0 < Real.sqrt τ := Real.sqrt_pos.mpr hτ
  have key : -(2 * ℓ * y) + -(bv ℓ τ y ^ 2) / 2 = -(bu ℓ τ y ^ 2) / 2 := by
    unfold bu bv; field_simp; ring
  unfold stdNormalPdf
  rw [← mul_div_assoc, ← Real.exp_add, key]

lemma hasDerivAt_BV_path (ℓ τ0 y0 α β a : ℝ) (hℓ : 0 < ℓ) (hτ : 0 < τ0 + α * a) :
    HasDerivAt (fun b => BV ℓ (τ0 + α * b) (y0 + β * b))
      (α * BVt ℓ (τ0 + α * a) (y0 + β * a) + β * BVy ℓ (τ0 + α * a) (y0 + β * a)) a := by
  have hs0 : 0 < Real.sqrt (τ0 + α * a) := Real.sqrt_pos.mpr hτ
  have hss : Real.sqrt (τ0 + α * a) * Real.sqrt (τ0 + α * a) = τ0 + α * a :=
    Real.mul_self_sqrt hτ.le
  have hτd : HasDerivAt (fun b => τ0 + α * b) α a := by
    simpa using ((hasDerivAt_id a).const_mul α).const_add τ0
  have hyd : HasDerivAt (fun b => y0 + β * b) β a := by
    simpa using ((hasDerivAt_id a).const_mul β).const_add y0
  have hsd : HasDerivAt (fun b => Real.sqrt (τ0 + α * b)) (α / (2 * Real.sqrt (τ0 + α * a))) a :=
    hτd.sqrt hτ.ne'
  have hud := (hyd.div hsd hs0.ne').add (hsd.const_mul ℓ)
  have hvd := (hsd.const_mul ℓ).sub (hyd.div hsd hs0.ne')
  have hud' : HasDerivAt (fun b => bu ℓ (τ0 + α * b) (y0 + β * b))
      ((β * Real.sqrt (τ0 + α * a) - (y0 + β * a) * (α / (2 * Real.sqrt (τ0 + α * a)))) /
        Real.sqrt (τ0 + α * a) ^ 2 + ℓ * (α / (2 * Real.sqrt (τ0 + α * a)))) a := hud
  have hvd' : HasDerivAt (fun b => bv ℓ (τ0 + α * b) (y0 + β * b))
      (ℓ * (α / (2 * Real.sqrt (τ0 + α * a))) - (β * Real.sqrt (τ0 + α * a) -
        (y0 + β * a) * (α / (2 * Real.sqrt (τ0 + α * a)))) / Real.sqrt (τ0 + α * a) ^ 2) a := hvd
  have hsu : Real.sqrt (τ0 + α * a) * bu ℓ (τ0 + α * a) (y0 + β * a) =
      (y0 + β * a) + ℓ * (τ0 + α * a) := by
    unfold bu; field_simp; rw [Real.sq_sqrt hτ.le]
  have hid := b_pdf_id ℓ (τ0 + α * a) (y0 + β * a) hτ
  set s := Real.sqrt (τ0 + α * a) with hsdef
  set u := bu ℓ (τ0 + α * a) (y0 + β * a) with hu
  set v := bv ℓ (τ0 + α * a) (y0 + β * a) with hv
  set u' := (β * s - (y0 + β * a) * (α / (2 * s))) / s ^ 2 + ℓ * (α / (2 * s)) with hu'
  set v' := ℓ * (α / (2 * s)) - (β * s - (y0 + β * a) * (α / (2 * s))) / s ^ 2 with hv'
  set E := Real.exp (-(2 * ℓ * (y0 + β * a))) with hEdef
  have hA : HasDerivAt (fun b => Real.sqrt (τ0 + α * b) * stdNormalPdf (bu ℓ (τ0 + α * b) (y0 + β * b))
      - ((y0 + β * b) + ℓ * (τ0 + α * b)) * (1 - stdNormalCdf (bu ℓ (τ0 + α * b) (y0 + β * b))))
      (α / (2 * s) * stdNormalPdf u - (β + ℓ * α) * (1 - stdNormalCdf u)) a := by
    have h := (hsd.mul ((g_pdf_deriv u).comp a hud')).sub ((hyd.add (hτd.const_mul ℓ)).mul
      ((hasDerivAt_const a (1:ℝ)).sub ((g_cdf_deriv u).comp a hud')))
    refine h.congr_deriv ?_
    simp only [Function.comp_apply, Pi.add_apply, Pi.sub_apply, Pi.mul_apply]
    linear_combination (-(stdNormalPdf u) * u') * hsu
  have hE : HasDerivAt (fun b => Real.exp (-(2 * ℓ * (y0 + β * b)))) (E * (-(2 * ℓ * β))) a := by
    have := ((hyd.const_mul (2 * ℓ)).neg).exp
    exact this.congr_deriv rfl
  have hB : HasDerivAt (fun b => Real.exp (-(2 * ℓ * (y0 + β * b))) *
        stdNormalCdf (bv ℓ (τ0 + α * b) (y0 + β * b)) -
        (1 - stdNormalCdf (bu ℓ (τ0 + α * b) (y0 + β * b))))
      (-(2 * ℓ * β) * (E * stdNormalCdf v) + stdNormalPdf u * (2 * ℓ * (α / (2 * s)))) a := by
    have h := (hE.mul ((g_cdf_deriv v).comp a hvd')).sub
      ((hasDerivAt_const a (1:ℝ)).sub ((g_cdf_deriv u).comp a hud'))
    refine h.congr_deriv ?_
    simp only [Function.comp_apply, Pi.add_apply, Pi.sub_apply, Pi.mul_apply]
    have huv : u' + v' = 2 * ℓ * (α / (2 * s)) := by rw [hu', hv']; ring
    linear_combination v' * hid - stdNormalPdf u * huv
  have hC := hA.add (hB.div_const (2 * ℓ))
  refine hC.congr_deriv ?_
  unfold BVt BVy
  rw [← hsdef, ← hu, ← hv, ← hEdef]
  have hl : ℓ ≠ 0 := hℓ.ne'
  have hsne : s ≠ 0 := hs0.ne'
  field_simp
  ring

end LostSalesRQ

namespace LostSalesRQ

open MeasureTheory ProbabilityTheory Filter Set Topology

lemma hasDerivAt_BV_y (ℓ τ y : ℝ) (hℓ : 0 < ℓ) (hτ : 0 < τ) :
    HasDerivAt (fun z => BV ℓ τ z) (BVy ℓ τ y) y := by
  have h := hasDerivAt_BV_path ℓ τ 0 0 1 y hℓ (by simpa using hτ)
  simp only [zero_mul, add_zero, zero_add, one_mul] at h
  exact h

lemma hasDerivAt_BV_t (ℓ τ y : ℝ) (hℓ : 0 < ℓ) (hτ : 0 < τ) :
    HasDerivAt (fun r => BV ℓ r y) (BVt ℓ τ y) τ := by
  have h := hasDerivAt_BV_path ℓ 0 y 1 0 τ hℓ (by simpa using hτ)
  simp only [zero_mul, add_zero, zero_add, one_mul] at h
  exact h

lemma hasDerivAt_BVy_y (ℓ τ y : ℝ) (hτ : 0 < τ) :
    HasDerivAt (fun z => BVy ℓ τ z) (BVyy ℓ τ y) y := by
  have hs0 : 0 < Real.sqrt τ := Real.sqrt_pos.mpr hτ
  have hud : HasDerivAt (fun z => bu ℓ τ z) (1 / Real.sqrt τ) y :=
    ((hasDerivAt_id' y).div_const (Real.sqrt τ)).add_const (ℓ * Real.sqrt τ)
  have hvd : HasDerivAt (fun z => bv ℓ τ z) (-(1 / Real.sqrt τ)) y :=
    ((hasDerivAt_id' y).div_const (Real.sqrt τ)).const_sub (ℓ * Real.sqrt τ)
  have hE : HasDerivAt (fun z => Real.exp (-(2 * ℓ * z)))
      (Real.exp (-(2 * ℓ * y)) * (-(2 * ℓ * 1))) y :=
    (((hasDerivAt_id' y).const_mul (2 * ℓ)).neg).exp
  have h := ((hasDerivAt_const y (1:ℝ)).sub ((g_cdf_deriv _).comp y hud)).neg.sub
    (hE.mul ((g_cdf_deriv _).comp y hvd))
  refine h.congr_deriv ?_
  have hid := b_pdf_id ℓ τ y hτ
  simp only [Function.comp_apply]
  unfold BVyy
  linear_combination (1 / Real.sqrt τ) * hid

lemma BV_pde (ℓ τ y : ℝ) : BVt ℓ τ y = ℓ * BVy ℓ τ y + BVyy ℓ τ y / 2 := by
  unfold BVt BVy BVyy; ring

lemma BVy_zero (ℓ τ : ℝ) : BVy ℓ τ 0 = -1 := by
  unfold BVy bu bv; simp

lemma cdf_mono : Monotone stdNormalCdf :=
  (strictMono_of_deriv_pos (fun x => by rw [(g_cdf_deriv x).deriv]; exact g_pdf_pos x)).monotone

lemma pdf_anti {x x' : ℝ} (hx : 0 ≤ x) (hxx : x ≤ x') : stdNormalPdf x' ≤ stdNormalPdf x := by
  unfold stdNormalPdf
  apply div_le_div_of_nonneg_right _ (Real.sqrt_nonneg _)
  apply Real.exp_le_exp.mpr
  nlinarith

lemma BVyy_anti (ℓ τ : ℝ) (hℓ : 0 ≤ ℓ) (hτ : 0 < τ) {y y' : ℝ} (hy : 0 ≤ y) (hyy : y ≤ y') :
    BVyy ℓ τ y' ≤ BVyy ℓ τ y := by
  have hs0 : 0 < Real.sqrt τ := Real.sqrt_pos.mpr hτ
  unfold BVyy
  have hu : bu ℓ τ y ≤ bu ℓ τ y' := by
    unfold bu; have := div_le_div_of_nonneg_right hyy hs0.le; linarith
  have hu0 : 0 ≤ bu ℓ τ y := by unfold bu; positivity
  have h1 : stdNormalPdf (bu ℓ τ y') ≤ stdNormalPdf (bu ℓ τ y) := pdf_anti hu0 hu
  have hv : bv ℓ τ y' ≤ bv ℓ τ y := by
    unfold bv; have := div_le_div_of_nonneg_right hyy hs0.le; linarith
  have h2 : stdNormalCdf (bv ℓ τ y') ≤ stdNormalCdf (bv ℓ τ y) := cdf_mono hv
  have h3 : Real.exp (-(2 * ℓ * y')) ≤ Real.exp (-(2 * ℓ * y)) := by
    apply Real.exp_le_exp.mpr; nlinarith
  have h4 : Real.exp (-(2 * ℓ * y')) * stdNormalCdf (bv ℓ τ y') ≤
      Real.exp (-(2 * ℓ * y)) * stdNormalCdf (bv ℓ τ y) :=
    mul_le_mul h3 h2 (g_cdf_pos _).le (Real.exp_pos _).le
  have h5 : 2 * stdNormalPdf (bu ℓ τ y') / Real.sqrt τ ≤ 2 * stdNormalPdf (bu ℓ τ y) / Real.sqrt τ :=
    div_le_div_of_nonneg_right (by linarith) hs0.le
  nlinarith

lemma BV_nonneg (ℓ τ y : ℝ) (hℓ : 0 < ℓ) (hτ : 0 < τ) (hy : 0 ≤ y) : 0 ≤ BV ℓ τ y := by
  have hs0 : 0 < Real.sqrt τ := Real.sqrt_pos.mpr hτ
  have hss : Real.sqrt τ ^ 2 = τ := Real.sq_sqrt hτ.le
  have hsu : y + ℓ * τ = Real.sqrt τ * bu ℓ τ y := by unfold bu; field_simp; rw [hss]
  have hu0 : 0 < bu ℓ τ y := by unfold bu; positivity
  have hid := b_pdf_id ℓ τ y hτ
  have hP := g_pdf_pos (bu ℓ τ y)
  have h1 : bu ℓ τ y * (1 - stdNormalCdf (bu ℓ τ y)) ≤ stdNormalPdf (bu ℓ τ y) := by
    rw [g_tail_eq]
    have := g_I_neg_lt hu0
    have h2 : bu ℓ τ y * gI (-bu ℓ τ y) ≤ 1 := by
      rw [lt_div_iff₀ hu0] at this; linarith
    nlinarith
  have hpart2 : 0 ≤ Real.exp (-(2 * ℓ * y)) * stdNormalCdf (bv ℓ τ y) - (1 - stdNormalCdf (bu ℓ τ y)) := by
    have hv : stdNormalCdf (bv ℓ τ y) = stdNormalPdf (bv ℓ τ y) * gU (bv ℓ τ y) := by
      unfold gU; field_simp [(g_pdf_pos (bv ℓ τ y)).ne']
    have hu : 1 - stdNormalCdf (bu ℓ τ y) = stdNormalPdf (bu ℓ τ y) * gU (-bu ℓ τ y) := by
      rw [g_tail_eq, gU_eq]
    have hvu : -bu ℓ τ y ≤ bv ℓ τ y := by unfold bu bv; nlinarith
    have hmono := gU_strictMono.monotone hvu
    rw [hv, hu, ← mul_assoc, hid]
    nlinarith
  unfold BV
  rw [hsu]
  have : 0 ≤ (Real.exp (-(2 * ℓ * y)) * stdNormalCdf (bv ℓ τ y) - (1 - stdNormalCdf (bu ℓ τ y))) / (2 * ℓ) :=
    div_nonneg hpart2 (by positivity)
  nlinarith

lemma BV_drift (ℓ τ y : ℝ) (hℓ : 0 < ℓ) (hτ : 0 < τ) (hy : 0 ≤ y) :
    -BVt ℓ τ y - (1 - ℓ) * BVy ℓ τ y + BV ℓ τ (y + 1) - BV ℓ τ y ≤ 0 := by
  rw [BV_pde]
  -- Taylor: BV(y+1) - BV(y) ≤ BVy(y) + BVyy(y)/2
  have hk1 : ∀ r ∈ Icc (0:ℝ) 1, BVy ℓ τ (y + r) - BVy ℓ τ y - r * BVyy ℓ τ y ≤ 0 := by
    have hanti : AntitoneOn (fun r => BVy ℓ τ (y + r) - BVy ℓ τ y - r * BVyy ℓ τ y) (Icc 0 1) := by
      have hd : ∀ r, HasDerivAt (fun r => BVy ℓ τ (y + r) - BVy ℓ τ y - r * BVyy ℓ τ y)
          (BVyy ℓ τ (y + r) - BVyy ℓ τ y) r := by
        intro r
        have h1 := (hasDerivAt_BVy_y ℓ τ (y + r) hτ).comp r ((hasDerivAt_id' r).const_add y)
        have h2 := ((h1.sub_const (BVy ℓ τ y)).sub ((hasDerivAt_id' r).mul_const (BVyy ℓ τ y)))
        exact h2.congr_deriv (by ring)
      apply antitoneOn_of_deriv_nonpos (convex_Icc 0 1)
      · exact fun r _ => (hd r).continuousAt.continuousWithinAt
      · exact fun r _ => (hd r).differentiableAt.differentiableWithinAt
      · intro r hr
        rw [interior_Icc] at hr
        rw [(hd r).deriv]
        have := BVyy_anti ℓ τ hℓ.le hτ hy (show y ≤ y + r by linarith [hr.1])
        linarith
    intro r hr
    have := hanti ⟨le_rfl, zero_le_one⟩ hr hr.1
    simpa using this
  have hk : BV ℓ τ (y + 1) - BV ℓ τ y - BVy ℓ τ y - BVyy ℓ τ y / 2 ≤ 0 := by
    have hanti : AntitoneOn (fun r => BV ℓ τ (y + r) - BV ℓ τ y - r * BVy ℓ τ y -
        r ^ 2 / 2 * BVyy ℓ τ y) (Icc 0 1) := by
      have hd : ∀ r, HasDerivAt (fun r => BV ℓ τ (y + r) - BV ℓ τ y - r * BVy ℓ τ y -
          r ^ 2 / 2 * BVyy ℓ τ y) (BVy ℓ τ (y + r) - BVy ℓ τ y - r * BVyy ℓ τ y) r := by
        intro r
        have h1 := (hasDerivAt_BV_y ℓ τ (y + r) hℓ hτ).comp r ((hasDerivAt_id' r).const_add y)
        have h2 := (((h1.sub_const (BV ℓ τ y)).sub ((hasDerivAt_id' r).mul_const (BVy ℓ τ y))).sub
          (((hasDerivAt_pow 2 r).div_const 2).mul_const (BVyy ℓ τ y)))
        exact h2.congr_deriv (by simp)
      apply antitoneOn_of_deriv_nonpos (convex_Icc 0 1)
      · exact fun r _ => (hd r).continuousAt.continuousWithinAt
      · exact fun r _ => (hd r).differentiableAt.differentiableWithinAt
      · intro r hr
        rw [interior_Icc] at hr
        rw [(hd r).deriv]
        exact hk1 r ⟨hr.1.le, hr.2.le⟩
    have := hanti ⟨le_rfl, zero_le_one⟩ ⟨zero_le_one, le_rfl⟩ zero_le_one
    simp at this
    linarith
  linarith

lemma BV_at_zero (ℓ T : ℝ) (hℓ : 0 < ℓ) (hT : 0 < T) :
    BV ℓ T 0 = Real.sqrt T * brownianProfile (ℓ * Real.sqrt T) := by
  have hs0 : 0 < Real.sqrt T := Real.sqrt_pos.mpr hT
  have hss : Real.sqrt T ^ 2 = T := Real.sq_sqrt hT.le
  have hz : ℓ * Real.sqrt T ≠ 0 := by positivity
  unfold BV bu bv brownianProfile
  rw [if_neg hz]
  simp only [zero_div, zero_add, sub_zero, mul_zero, neg_zero, Real.exp_zero, one_mul]
  set s := Real.sqrt T
  rw [← hss]
  field_simp
  ring

lemma BV_cont_zero (ℓ T : ℝ) (hℓ : 0 < ℓ) (hT : 0 < T) :
    ContinuousAt (fun r => BV ℓ r 0) T :=
  (hasDerivAt_BV_t ℓ T 0 hℓ hT).continuousAt

end LostSalesRQ

namespace LostSalesRQ

open MeasureTheory ProbabilityTheory Filter Set Topology

lemma cdf_cont : Continuous stdNormalCdf :=
  continuous_iff_continuousAt.mpr (fun z => (g_cdf_deriv z).continuousAt)

lemma BV_contOn (ℓ : ℝ) : ContinuousOn (fun p : ℝ × ℝ => BV ℓ p.1 p.2) {p | 0 < p.1} := by
  have hΦ := cdf_cont
  have hφ := g_pdf_cont
  unfold BV bu bv
  have hs : ∀ p ∈ {p : ℝ × ℝ | 0 < p.1}, Real.sqrt p.1 ≠ 0 := fun p hp =>
    (Real.sqrt_pos.mpr hp).ne'
  fun_prop (disch := assumption)

lemma hasDerivAt_BV_back (ℓ τ0 y0 β a : ℝ) (hℓ : 0 < ℓ) (hτ : 0 < τ0 - a) :
    HasDerivAt (fun b => BV ℓ (τ0 - b) (y0 - β * b))
      (-BVt ℓ (τ0 - a) (y0 - β * a) - β * BVy ℓ (τ0 - a) (y0 - β * a)) a := by
  have h := hasDerivAt_BV_path ℓ τ0 y0 (-1) (-β) a hℓ (by linarith)
  have hf : (fun b => BV ℓ (τ0 + -1 * b) (y0 + -β * b)) = fun b => BV ℓ (τ0 - b) (y0 - β * b) := by
    funext b; congr 1 <;> ring
  rw [hf] at h
  have e1 : τ0 + -1 * a = τ0 - a := by ring
  have e2 : y0 + -β * a = y0 - β * a := by ring
  rw [e1, e2] at h
  exact h.congr_deriv (by ring)

lemma psi_anti (ℓ τ0 y0 β lam κ a0 a1 : ℝ) (hℓ : 0 < ℓ) (h01 : a0 ≤ a1) (hτ : 0 < τ0 - a1)
    (hy : ∀ a ∈ Icc a0 a1, 0 ≤ y0 - β * a)
    (hcond : ∀ a ∈ Icc a0 a1, lam - β * BVy ℓ (τ0 - a) (y0 - β * a) =
      -(1 - ℓ) * BVy ℓ (τ0 - a) (y0 - β * a)) :
    Real.exp (-a1) * (lam * a1 + κ + BV ℓ (τ0 - a1) (y0 - β * a1)) +
      ∫ s in a0..a1, Real.exp (-s) * (lam * s + κ + BV ℓ (τ0 - s) (y0 + 1 - β * s)) ≤
    Real.exp (-a0) * (lam * a0 + κ + BV ℓ (τ0 - a0) (y0 - β * a0)) := by
  set k : ℝ → ℝ := fun s => Real.exp (-s) * (lam * s + κ + BV ℓ (τ0 - s) (y0 + 1 - β * s)) with hk
  have hkc : ContinuousOn k (Iio τ0) := by
    intro s hs
    have hs' : 0 < τ0 - s := by simp at hs; linarith
    have hd := hasDerivAt_BV_back ℓ τ0 (y0 + 1) β s hℓ hs'
    exact (((Real.continuous_exp.comp continuous_neg).continuousAt).mul
      ((continuousAt_const.mul continuousAt_id).add continuousAt_const |>.add hd.continuousAt)).continuousWithinAt
  have hsub : ∀ a, a ≤ a1 → Icc a0 a ⊆ Iio τ0 := fun a ha x hx => by
    simp only [mem_Iio]; linarith [hx.2]
  set ψ : ℝ → ℝ := fun a => Real.exp (-a) * (lam * a + κ + BV ℓ (τ0 - a) (y0 - β * a)) +
    ∫ s in a0..a, k s with hψ
  have hder : ∀ a, a0 ≤ a → a < τ0 → HasDerivAt ψ
      (Real.exp (-a) * (lam - BVt ℓ (τ0 - a) (y0 - β * a) - β * BVy ℓ (τ0 - a) (y0 - β * a) +
        BV ℓ (τ0 - a) (y0 - β * a + 1) - BV ℓ (τ0 - a) (y0 - β * a))) a := by
    intro a ha haτ
    have hτa : 0 < τ0 - a := by linarith
    have h1 := ((hasDerivAt_neg a).exp).mul ((((hasDerivAt_id' a).const_mul lam).add_const κ).add
      (hasDerivAt_BV_back ℓ τ0 y0 β a hℓ hτa))
    have hint : IntervalIntegrable k volume a0 a := by
      apply ContinuousOn.intervalIntegrable
      apply hkc.mono
      rw [uIcc_of_le ha]
      intro x hx; simp only [mem_Iio]; linarith [hx.2]
    have hmeas : StronglyMeasurableAtFilter k (𝓝 a) volume :=
      hkc.stronglyMeasurableAtFilter isOpen_Iio a haτ
    have h2 := intervalIntegral.integral_hasDerivAt_right hint hmeas (hkc.continuousAt (Iio_mem_nhds haτ))
    refine (h1.add h2).congr_deriv ?_
    simp only [hk, Pi.add_apply, Pi.mul_apply]
    have e : y0 + 1 - β * a = y0 - β * a + 1 := by ring
    rw [e]
    ring
  have hanti : AntitoneOn ψ (Icc a0 a1) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc a0 a1)
    · intro a ha
      exact (hder a ha.1 (by linarith [ha.2])).continuousAt.continuousWithinAt
    · intro a ha
      rw [interior_Icc] at ha
      exact (hder a ha.1.le (by linarith [ha.2])).differentiableAt.differentiableWithinAt
    · intro a ha
      rw [interior_Icc] at ha
      have haI : a ∈ Icc a0 a1 := ⟨ha.1.le, ha.2.le⟩
      rw [(hder a ha.1.le (by linarith [ha.2])).deriv]
      have hτa : 0 < τ0 - a := by linarith [ha.2]
      have hD := BV_drift ℓ (τ0 - a) (y0 - β * a) hℓ hτa (hy a haI)
      have hc := hcond a haI
      have : lam - BVt ℓ (τ0 - a) (y0 - β * a) - β * BVy ℓ (τ0 - a) (y0 - β * a) +
          BV ℓ (τ0 - a) (y0 - β * a + 1) - BV ℓ (τ0 - a) (y0 - β * a) ≤ 0 := by linarith
      exact mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le this
  have := hanti ⟨le_rfl, h01⟩ ⟨h01, le_rfl⟩ h01
  simp only [hψ, intervalIntegral.integral_same, add_zero] at this
  exact this

lemma psi_ineq (ℓ ε t y : ℝ) (hℓ : 0 < ℓ) (hℓ1 : ℓ ≤ 1) (hε : 0 < ε) (ht : 0 ≤ t) (hy : 0 ≤ y) :
    Real.exp (-t) * max ((1 - ℓ) * t - y) 0 +
      ∫ a in (0:ℝ)..t, Real.exp (-a) * (max ((1 - ℓ) * a - y) 0 +
        BV ℓ (t + ε - a) (1 + max (y - (1 - ℓ) * a) 0)) ≤ BV ℓ (t + ε) y := by
  set f := 1 - ℓ with hf
  have hf0 : 0 ≤ f := by linarith
  set g : ℝ → ℝ := fun a => Real.exp (-a) * (max (f * a - y) 0 +
        BV ℓ (t + ε - a) (1 + max (y - f * a) 0)) with hg
  have hgc : ContinuousOn g (Icc 0 t) := by
    have hm : MapsTo (fun a : ℝ => (t + ε - a, 1 + max (y - f * a) 0)) (Icc 0 t) {p | 0 < p.1} := by
      intro a ha; simp only [mem_ofPred_eq]; linarith [ha.2]
    have hB := (BV_contOn ℓ).comp (by fun_prop) hm
    exact ((Real.continuous_exp.comp continuous_neg).continuousOn).mul
      ((by fun_prop : Continuous fun a : ℝ => max (f * a - y) 0).continuousOn.add hB)
  rcases le_or_gt (f * t) y with hA | hB
  · -- the fluid line stays below y
    have h := psi_anti ℓ (t + ε) y f 0 0 0 t hℓ ht (by linarith)
      (fun a ha => by nlinarith [ha.2]) (fun a _ => by ring)
    have hcong : ∫ a in (0:ℝ)..t, g a = ∫ s in (0:ℝ)..t, Real.exp (-s) * (0 * s + 0 +
        BV ℓ (t + ε - s) (y + 1 - f * s)) := by
      apply intervalIntegral.integral_congr
      intro a ha
      rw [uIcc_of_le ht] at ha
      have h1 : f * a ≤ y := by nlinarith [ha.2]
      simp only [hg, max_eq_right (by linarith : f * a - y ≤ 0),
        max_eq_left (by linarith : 0 ≤ y - f * a)]
      congr 2 <;> ring_nf
    have hBV := BV_nonneg ℓ (t + ε - t) (y - f * t) hℓ (by linarith) (by linarith)
    rw [max_eq_right (by linarith : f * t - y ≤ 0), mul_zero, zero_add]
    show ∫ a in (0:ℝ)..t, g a ≤ _
    rw [hcong]
    simp only [neg_zero, Real.exp_zero, one_mul, zero_mul, mul_zero, zero_add, sub_zero] at h ⊢
    have := mul_nonneg (Real.exp_pos (-t)).le hBV
    linarith
  · have hfpos : 0 < f := by
      by_contra h; push Not at h
      have : f * t ≤ 0 := mul_nonpos_of_nonpos_of_nonneg h ht
      linarith
    set c := y / f with hc
    have hc0 : 0 ≤ c := div_nonneg hy hfpos.le
    have hct : c < t := by rw [hc, div_lt_iff₀ hfpos]; linarith
    have hfc : f * c = y := by rw [hc]; field_simp
    have h1 := psi_anti ℓ (t + ε) y f 0 0 0 c hℓ hc0 (by linarith)
      (fun a ha => by nlinarith [ha.2]) (fun a _ => by ring)
    have h2 := psi_anti ℓ (t + ε) 0 0 f (-y) c t hℓ hct.le (by linarith)
      (fun a _ => by simp) (fun a _ => by simp only [zero_mul, sub_zero, BVy_zero]; rw [hf]; ring)
    have hint : ∀ a b, 0 ≤ a → a ≤ b → b ≤ t → IntervalIntegrable g volume a b := by
      intro a b ha hab hbt
      apply ContinuousOn.intervalIntegrable
      apply hgc.mono
      rw [uIcc_of_le hab]
      exact Icc_subset_Icc ha hbt
    have hsplit := intervalIntegral.integral_add_adjacent_intervals (hint 0 c le_rfl hc0 hct.le)
      (hint c t hc0 hct.le le_rfl)
    have hcong1 : ∫ a in (0:ℝ)..c, g a = ∫ s in (0:ℝ)..c, Real.exp (-s) * (0 * s + 0 +
        BV ℓ (t + ε - s) (y + 1 - f * s)) := by
      apply intervalIntegral.integral_congr
      intro a ha
      rw [uIcc_of_le hc0] at ha
      have h1 : f * a ≤ y := by rw [← hfc]; nlinarith [ha.2]
      simp only [hg, max_eq_right (by linarith : f * a - y ≤ 0),
        max_eq_left (by linarith : 0 ≤ y - f * a)]
      congr 2 <;> ring_nf
    have hcong2 : ∫ a in c..t, g a = ∫ s in c..t, Real.exp (-s) * (f * s + -y +
        BV ℓ (t + ε - s) (0 + 1 - 0 * s)) := by
      apply intervalIntegral.integral_congr
      intro a ha
      rw [uIcc_of_le hct.le] at ha
      have h1 : y ≤ f * a := by rw [← hfc]; nlinarith [ha.1]
      simp only [hg, max_eq_left (by linarith : 0 ≤ f * a - y),
        max_eq_right (by linarith : y - f * a ≤ 0)]
      congr 2 <;> ring_nf
    have hBV := BV_nonneg ℓ (t + ε - t) (0 - 0 * t) hℓ (by linarith) (by simp)
    rw [max_eq_left (by linarith : 0 ≤ f * t - y)]
    show Real.exp (-t) * (f * t - y) + ∫ a in (0:ℝ)..t, g a ≤ _
    rw [← hsplit, hcong1, hcong2]
    simp only [neg_zero, Real.exp_zero, one_mul, zero_mul, mul_zero, zero_add, sub_zero] at h1 h2 ⊢
    simp only [hfc, sub_self, add_neg_cancel, zero_add] at h1 h2
    have := mul_nonneg (Real.exp_pos (-t)).le hBV
    simp only [zero_mul, sub_zero] at this
    linarith

end LostSalesRQ

namespace LostSalesRQ

open MeasureTheory ProbabilityTheory Filter Set Topology

/-- Drop the first interarrival time. -/
def tailPath (ξ : DemandPath) : DemandPath := fun n => ξ (n + 1)

lemma measurable_tailPath : Measurable tailPath :=
  measurable_pi_lambda _ (fun n => measurable_pi_apply (n + 1))

lemma arrivalEpoch_tail (ξ : DemandPath) (k : ℕ) :
    arrivalEpoch ξ (k + 1) = ξ 0 + arrivalEpoch (tailPath ξ) k := by
  unfold arrivalEpoch tailPath
  rw [Finset.sum_range_succ' _ (k + 1)]
  ring

/-- The term min (f S_k) (f t) - k of the discrete maximum. -/
noncomputable def dterm (f t : ℝ) (ξ : DemandPath) (k : ℕ) : ℝ :=
  min (f * arrivalEpoch ξ k) (f * t) - k

/-- Partial maxima over k ≤ K. -/
noncomputable def pmx (f : ℝ) : ℕ → ℝ → DemandPath → ℝ
  | 0, t, ξ => dterm f t ξ 0
  | K + 1, t, ξ => max (pmx f K t ξ) (dterm f t ξ (K + 1))

lemma dterm_succ (f t : ℝ) (ξ : DemandPath) (k : ℕ) :
    dterm f t ξ (k + 1) = f * ξ 0 - 1 + dterm f (t - ξ 0) (tailPath ξ) k := by
  unfold dterm
  rw [arrivalEpoch_tail]
  have : f * t = f * ξ 0 + f * (t - ξ 0) := by ring
  rw [this, mul_add, min_add_add_left]
  push_cast; ring

lemma dterm_zero (f t : ℝ) (ξ : DemandPath) : dterm f t ξ 0 = min (f * ξ 0) (f * t) := by
  unfold dterm; simp [arrivalEpoch]

lemma pmx_rec (f : ℝ) (K : ℕ) (t : ℝ) (ξ : DemandPath) :
    pmx f (K + 1) t ξ = max (dterm f t ξ 0) (f * ξ 0 - 1 + pmx f K (t - ξ 0) (tailPath ξ)) := by
  induction K with
  | zero => simp only [pmx, dterm_succ]
  | succ K ih =>
    rw [pmx, ih, dterm_succ, pmx, ← max_add_add_left, max_assoc]

lemma pmx_zero_eq (f t : ℝ) (ξ : DemandPath) :
    pmx f 0 t ξ = max (dterm f t ξ 0) (f * ξ 0 - 1 + min 0 (f * (t - ξ 0))) := by
  simp only [pmx]
  rw [dterm_zero]
  have : f * ξ 0 - 1 + min 0 (f * (t - ξ 0)) = min (f * ξ 0) (f * t) - 1 := by
    rw [← min_add_add_left]
    have e1 : f * ξ 0 - 1 + 0 = f * ξ 0 - 1 := by ring
    have e2 : f * ξ 0 - 1 + f * (t - ξ 0) = f * t - 1 := by ring
    rw [e1, e2, min_sub_sub_right]
  rw [this]
  exact (max_eq_left (by linarith)).symm

lemma pmx_le (f : ℝ) (K : ℕ) (t : ℝ) (ξ : DemandPath) : pmx f K t ξ ≤ f * t := by
  have hd : ∀ k, dterm f t ξ k ≤ f * t := fun k => by
    unfold dterm; have := min_le_right (f * arrivalEpoch ξ k) (f * t)
    have : (0:ℝ) ≤ k := Nat.cast_nonneg k; linarith
  induction K with
  | zero => exact hd 0
  | succ K ih => exact max_le ih (hd _)

lemma dterm_le_pmx (f t : ℝ) (ξ : DemandPath) (k : ℕ) : dterm f t ξ k ≤ pmx f k t ξ := by
  cases k with
  | zero => exact le_rfl
  | succ k => exact le_max_right _ _

lemma pmx_mono (f t : ℝ) (ξ : DemandPath) : Monotone (fun K => pmx f K t ξ) :=
  monotone_nat_of_le_succ (fun K => le_max_left _ _)

lemma measurable_dterm (f : ℝ) (k : ℕ) :
    Measurable (fun p : ℝ × DemandPath => dterm f p.1 p.2 k) := by
  unfold dterm
  exact ((((measurable_arrivalEpoch k).comp measurable_snd).const_mul f).min
    (measurable_fst.const_mul f)).sub_const _

lemma measurable_pmx (f : ℝ) (K : ℕ) :
    Measurable (fun p : ℝ × DemandPath => pmx f K p.1 p.2) := by
  induction K with
  | zero => exact measurable_dterm f 0
  | succ K ih => exact ih.max (measurable_dterm f (K + 1))

lemma measurable_BV (ℓ : ℝ) : Measurable (fun p : ℝ × ℝ => BV ℓ p.1 p.2) := by
  have hΦ := cdf_cont.measurable
  have hφ := g_pdf_cont.measurable
  unfold BV bu bv
  fun_prop

lemma ofReal_max0 (x : ℝ) : ENNReal.ofReal x = ENNReal.ofReal (max x 0) := by
  rcases le_total x 0 with h | h
  · rw [max_eq_right h, ENNReal.ofReal_of_nonpos h, ENNReal.ofReal_zero]
  · rw [max_eq_left h]

lemma max_split (z q : ℝ) :
    max (max z (z - 1 + q)) 0 = max z 0 + max (q - (1 + max (-z) 0)) 0 := by
  simp only [max_def]; split_ifs <;> linarith

lemma lint_exp_Iic_eq' (h : ℝ) (hh : 0 ≤ h) (G : ℝ → ℝ) (hGm : Measurable G)
    (hGc : ContinuousOn G (Icc 0 h)) (hG0 : ∀ a ∈ Icc 0 h, 0 ≤ G a) :
    ∫⁻ a in Iic h, ENNReal.ofReal (G a) ∂(expMeasure 1) =
      ENNReal.ofReal (∫ a in (0:ℝ)..h, Real.exp (-a) * G a) := by
  rw [expMeasure_eq_withDensity, setLIntegral_withDensity_eq_setLIntegral_mul _
    (measurable_exponentialPDF' 1) hGm.ennreal_ofReal measurableSet_Iic]
  have h1 : ∫⁻ a in Iic h, (exponentialPDF 1 * fun a => ENNReal.ofReal (G a)) a =
      ∫⁻ a in Icc 0 h, ENNReal.ofReal (Real.exp (-a) * G a) := by
    rw [← lintegral_indicator measurableSet_Iic, ← lintegral_indicator measurableSet_Icc]
    apply lintegral_congr
    intro a
    by_cases ha : 0 ≤ a
    · by_cases hah : a ≤ h
      · rw [indicator_of_mem (show a ∈ Iic h from hah),
          indicator_of_mem (show a ∈ Icc 0 h from ⟨ha, hah⟩)]
        simp only [Pi.mul_apply]
        rw [exponentialPDF_of_nonneg ha, ← ENNReal.ofReal_mul (by positivity)]
        congr 1; ring
      · rw [indicator_of_notMem (show a ∉ Iic h by simpa using hah),
          indicator_of_notMem (show a ∉ Icc 0 h by simp [hah])]
    · push Not at ha
      rw [indicator_of_notMem (show a ∉ Icc 0 h by simp [not_le.mpr ha])]
      by_cases hah : a ≤ h
      · rw [indicator_of_mem (show a ∈ Iic h from hah)]
        simp [Pi.mul_apply, exponentialPDF_of_neg ha]
      · rw [indicator_of_notMem (show a ∉ Iic h by simpa using hah)]
  rw [h1, intervalIntegral.integral_of_le hh, ← integral_Icc_eq_integral_Ioc,
    ofReal_integral_eq_lintegral_ofReal]
  · exact (((Real.continuous_exp.comp continuous_neg).continuousOn).mul hGc).integrableOn_Icc
  · filter_upwards [ae_restrict_mem measurableSet_Icc] with a ha
    exact mul_nonneg (Real.exp_pos _).le (hG0 a ha)

lemma step_bound (ℓ ε : ℝ) (hℓ : 0 < ℓ) (hℓ1 : ℓ ≤ 1) (hε : 0 < ε) (F : ℝ → DemandPath → ℝ)
    (hFm : Measurable (fun p : ℝ × DemandPath => F p.1 p.2))
    (hFle : ∀ s ξ, F s ξ ≤ (1 - ℓ) * s)
    (hFb : ∀ s y', 0 ≤ s → 0 ≤ y' →
      ∫⁻ ξ, ENNReal.ofReal (F s ξ - y') ∂interarrivalLaw ≤ ENNReal.ofReal (BV ℓ (s + ε) y'))
    (t y : ℝ) (ht : 0 ≤ t) (hy : 0 ≤ y) :
    ∫⁻ ξ, ENNReal.ofReal (max (dterm (1 - ℓ) t ξ 0)
      ((1 - ℓ) * ξ 0 - 1 + F (t - ξ 0) (tailPath ξ)) - y) ∂interarrivalLaw ≤
      ENNReal.ofReal (BV ℓ (t + ε) y) := by
  set f := 1 - ℓ with hf
  have hf0 : 0 ≤ f := by linarith
  set G : DemandPath → ENNReal := fun ξ => ENNReal.ofReal (max (dterm f t ξ 0)
      (f * ξ 0 - 1 + F (t - ξ 0) (tailPath ξ)) - y) with hG
  have hGm : Measurable G := by
    have h1 : Measurable (fun ξ : DemandPath => dterm f t ξ 0) :=
      (measurable_dterm f 0).comp (measurable_const.prodMk measurable_id)
    have h2 : Measurable (fun ξ : DemandPath => F (t - ξ 0) (tailPath ξ)) :=
      hFm.comp ((measurable_const.sub (measurable_pi_apply 0)).prodMk measurable_tailPath)
    exact ((h1.max (((measurable_pi_apply 0).const_mul f).sub_const 1 |>.add h2)).sub_const y).ennreal_ofReal
  -- the bound on the inner integral
  set Λ : ℝ → ℝ := fun a => max (f * a - y) 0 + BV ℓ (t + ε - a) (1 + max (y - f * a) 0) with hΛ
  have hinner : ∀ a, ∫⁻ ξ', G (consPath (a, ξ')) ∂interarrivalLaw ≤
      (Ioi t).indicator (fun _ => ENNReal.ofReal (max (f * t - y) 0)) a +
      (Iic t).indicator (fun a => ENNReal.ofReal (Λ a)) a := by
    intro a
    have hcons : ∀ ξ', G (consPath (a, ξ')) = ENNReal.ofReal
        (max (min (f * a) (f * t)) (f * a - 1 + F (t - a) ξ') - y) := by
      intro ξ'
      simp only [hG, dterm_zero]
      rfl
    simp_rw [hcons]
    by_cases hat : t < a
    · rw [indicator_of_mem (show a ∈ Ioi t from hat), indicator_of_notMem (show a ∉ Iic t by
        simpa using hat), add_zero]
      have hval : ∀ ξ', max (min (f * a) (f * t)) (f * a - 1 + F (t - a) ξ') - y = f * t - y := by
        intro ξ'
        have h1 : min (f * a) (f * t) = f * t := min_eq_right (by nlinarith)
        have h2 := hFle (t - a) ξ'
        rw [h1, max_eq_left (by nlinarith)]
      simp_rw [hval, lintegral_const, measure_univ, mul_one]
      rw [← ofReal_max0]
    · push Not at hat
      rw [indicator_of_notMem (show a ∉ Ioi t by simpa using hat), indicator_of_mem
        (show a ∈ Iic t from hat), zero_add]
      have hval : ∀ ξ', ENNReal.ofReal (max (min (f * a) (f * t)) (f * a - 1 + F (t - a) ξ') - y) =
          ENNReal.ofReal (max (f * a - y) 0) +
            ENNReal.ofReal (F (t - a) ξ' - (1 + max (y - f * a) 0)) := by
        intro ξ'
        have h1 : min (f * a) (f * t) = f * a := min_eq_left (by nlinarith)
        rw [h1, ofReal_max0, ofReal_max0 (F (t - a) ξ' - _), ← ENNReal.ofReal_add (le_max_right _ _)
          (le_max_right _ _)]
        congr 1
        have := max_split (f * a - y) (F (t - a) ξ')
        have e1 : max (f * a) (f * a - 1 + F (t - a) ξ') - y =
            max (f * a - y) (f * a - y - 1 + F (t - a) ξ') := by
          rw [← max_sub_sub_right]; ring_nf
        rw [e1, this]
        congr 2; ring_nf
      simp_rw [hval]
      rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one]
      have hb := hFb (t - a) (1 + max (y - f * a) 0) (by linarith) (by positivity)
      have e : t - a + ε = t + ε - a := by ring
      rw [e] at hb
      have hBV := BV_nonneg ℓ (t + ε - a) (1 + max (y - f * a) 0) hℓ (by linarith) (by positivity)
      calc ENNReal.ofReal (max (f * a - y) 0) +
            ∫⁻ ξ', ENNReal.ofReal (F (t - a) ξ' - (1 + max (y - f * a) 0)) ∂interarrivalLaw
          ≤ ENNReal.ofReal (max (f * a - y) 0) + ENNReal.ofReal (BV ℓ (t + ε - a) (1 + max (y - f * a) 0)) := by
            gcongr
        _ = ENNReal.ofReal (Λ a) := by
            rw [hΛ, ENNReal.ofReal_add (le_max_right _ _) hBV]
  have hΛm : Measurable Λ := by
    have hp : Measurable (fun a : ℝ => (t + ε - a, 1 + max (y - f * a) 0)) := by fun_prop
    have hB := (measurable_BV ℓ).comp hp
    exact (by fun_prop : Measurable fun a : ℝ => max (f * a - y) 0).add hB
  have hΛc : ContinuousOn Λ (Icc 0 t) := by
    have hm : MapsTo (fun a : ℝ => (t + ε - a, 1 + max (y - f * a) 0)) (Icc 0 t) {p | 0 < p.1} := by
      intro a ha; simp only [mem_ofPred_eq]; linarith [ha.2]
    exact (by fun_prop : Continuous fun a : ℝ => max (f * a - y) 0).continuousOn.add
      ((BV_contOn ℓ).comp (by fun_prop) hm)
  have hΛ0 : ∀ a ∈ Icc 0 t, 0 ≤ Λ a := fun a ha =>
    add_nonneg (le_max_right _ _) (BV_nonneg ℓ _ _ hℓ (by linarith [ha.2]) (by positivity))
  calc ∫⁻ ξ, G ξ ∂interarrivalLaw
      = ∫⁻ ξ, G ξ ∂(((expMeasure 1).prod interarrivalLaw).map consPath) := by rw [law_shift]
    _ = ∫⁻ p, G (consPath p) ∂((expMeasure 1).prod interarrivalLaw) :=
        lintegral_map hGm measurable_consPath
    _ = ∫⁻ a, ∫⁻ ξ', G (consPath (a, ξ')) ∂interarrivalLaw ∂(expMeasure 1) :=
        lintegral_prod _ (hGm.comp measurable_consPath).aemeasurable
    _ ≤ ∫⁻ a, ((Ioi t).indicator (fun _ => ENNReal.ofReal (max (f * t - y) 0)) a +
        (Iic t).indicator (fun a => ENNReal.ofReal (Λ a)) a) ∂(expMeasure 1) :=
        lintegral_mono hinner
    _ = ENNReal.ofReal (max (f * t - y) 0) * expMeasure 1 (Ioi t) +
        ∫⁻ a in Iic t, ENNReal.ofReal (Λ a) ∂(expMeasure 1) := by
        rw [lintegral_add_left (measurable_const.indicator measurableSet_Ioi),
          lintegral_indicator_const measurableSet_Ioi, lintegral_indicator measurableSet_Iic]
    _ = ENNReal.ofReal (Real.exp (-t) * max (f * t - y) 0 +
          ∫ a in (0:ℝ)..t, Real.exp (-a) * Λ a) := by
        rw [exp_Ioi t ht, lint_exp_Iic_eq' t ht Λ hΛm hΛc hΛ0, ← ENNReal.ofReal_mul (le_max_right _ _),
          ← ENNReal.ofReal_add (by positivity)]
        · ring_nf
        · apply intervalIntegral.integral_nonneg ht
          intro a ha; exact mul_nonneg (Real.exp_pos _).le (hΛ0 a ha)
    _ ≤ ENNReal.ofReal (BV ℓ (t + ε) y) :=
        ENNReal.ofReal_le_ofReal (psi_ineq ℓ ε t y hℓ hℓ1 hε ht hy)

lemma pmx_bound (ℓ ε : ℝ) (hℓ : 0 < ℓ) (hℓ1 : ℓ ≤ 1) (hε : 0 < ε) (K : ℕ) :
    ∀ t y, 0 ≤ t → 0 ≤ y → ∫⁻ ξ, ENNReal.ofReal (pmx (1 - ℓ) K t ξ - y) ∂interarrivalLaw ≤
      ENNReal.ofReal (BV ℓ (t + ε) y) := by
  induction K with
  | zero =>
    intro t y ht hy
    simp_rw [pmx_zero_eq]
    refine step_bound ℓ ε hℓ hℓ1 hε (fun s _ => min 0 ((1 - ℓ) * s)) (by fun_prop)
      (fun s _ => min_le_right _ _) (fun s y' hs hy' => ?_) t y ht hy
    have h0 : ENNReal.ofReal (min 0 ((1 - ℓ) * s) - y') = 0 :=
      ENNReal.ofReal_of_nonpos (by linarith [min_le_left 0 ((1 - ℓ) * s)])
    simp only [h0, lintegral_zero]
    exact zero_le
  | succ K ih =>
    intro t y ht hy
    simp_rw [pmx_rec]
    exact step_bound ℓ ε hℓ hℓ1 hε (fun s ξ => pmx (1 - ℓ) K s ξ) (measurable_pmx _ K)
      (fun s ξ => pmx_le _ K s ξ) ih t y ht hy

end LostSalesRQ

namespace LostSalesRQ

open MeasureTheory ProbabilityTheory Filter Set Topology

lemma emx_le_BV (T ℓ ε : ℝ) (hT : 0 ≤ T) (hℓ : 0 < ℓ) (hℓ1 : ℓ ≤ 1) (hε : 0 < ε) :
    expectedMaxExcess T ℓ ≤ BV ℓ (T + ε) 0 := by
  set f := 1 - ℓ with hf
  have hf0 : 0 ≤ f := by linarith
  have hmeasK : ∀ K, Measurable (fun ξ : DemandPath => ENNReal.ofReal (pmx f K T ξ)) := fun K =>
    ((measurable_pmx f K).comp (measurable_const.prodMk measurable_id)).ennreal_ofReal
  have hpt : ∀ ξ, ENNReal.ofReal (maxDisc T f ξ) ≤ ⨆ K, ENNReal.ofReal (pmx f K T ξ) := by
    intro ξ
    unfold maxDisc
    rw [Monotone.map_ciSup_of_continuousAt ENNReal.continuous_ofReal.continuousAt
      (fun _ _ h => ENNReal.ofReal_le_ofReal h) (maxDisc_bdd T f ξ)]
    exact iSup_mono (fun k => ENNReal.ofReal_le_ofReal (dterm_le_pmx f T ξ k))
  have hmono : Monotone (fun K => fun ξ : DemandPath => ENNReal.ofReal (pmx f K T ξ)) :=
    fun K K' h ξ => ENNReal.ofReal_le_ofReal (pmx_mono f T ξ h)
  have hlint : ∫⁻ ξ, ENNReal.ofReal (maxDisc T f ξ) ∂interarrivalLaw ≤
      ENNReal.ofReal (BV ℓ (T + ε) 0) := by
    calc ∫⁻ ξ, ENNReal.ofReal (maxDisc T f ξ) ∂interarrivalLaw
        ≤ ∫⁻ ξ, ⨆ K, ENNReal.ofReal (pmx f K T ξ) ∂interarrivalLaw := lintegral_mono hpt
      _ = ⨆ K, ∫⁻ ξ, ENNReal.ofReal (pmx f K T ξ) ∂interarrivalLaw := lintegral_iSup hmeasK hmono
      _ ≤ ENNReal.ofReal (BV ℓ (T + ε) 0) := by
        refine iSup_le (fun K => ?_)
        have := pmx_bound ℓ ε hℓ hℓ1 hε K T 0 hT le_rfl
        simpa only [sub_zero] using this
  have hnn : 0 ≤ᵐ[interarrivalLaw] maxDisc T f := by
    filter_upwards [ae_goodSet T] with ξ hξ
    exact maxDisc_nonneg T f hT hf0 ξ hξ.2.1.le
  have heq : expectedMaxExcess T ℓ = ∫ ξ, maxDisc T f ξ ∂interarrivalLaw :=
    integral_congr_ae (ae_maxExcess_eq T f hT hf0)
  rw [heq, integral_eq_lintegral_of_nonneg_ae hnn (measurable_maxDisc T f).aestronglyMeasurable]
  exact ENNReal.toReal_le_of_le_ofReal (BV_nonneg ℓ _ 0 hℓ (by linarith) le_rfl) hlint

lemma emx_le_pos (T ℓ : ℝ) (hT : 0 < T) (hℓ : 0 < ℓ) (hℓ1 : ℓ ≤ 1) :
    expectedMaxExcess T ℓ ≤ Real.sqrt T * brownianProfile (ℓ * Real.sqrt T) := by
  rw [← BV_at_zero ℓ T hℓ hT]
  have ht : Tendsto (fun ε : ℝ => T + ε) (𝓝[>] 0) (𝓝 T) := by
    have : Tendsto (fun ε : ℝ => T + ε) (𝓝 0) (𝓝 (T + 0)) :=
      tendsto_const_nhds.add tendsto_id
    rw [add_zero] at this
    exact this.mono_left nhdsWithin_le_nhds
  have hlim := (BV_cont_zero ℓ T hℓ hT).tendsto.comp ht
  refine ge_of_tendsto hlim ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact emx_le_BV T ℓ ε hT.le hℓ hℓ1 hε

lemma cdf_zero : stdNormalCdf 0 = 1 / 2 := by
  have h1 := g_cdf_rep 0
  have h2 := g_tail_eq 0
  rw [neg_zero] at h2
  linarith

lemma bprof_zero : brownianProfile 0 = 2 * stdNormalPdf 0 := by
  unfold brownianProfile stdNormalPdf
  rw [if_pos rfl]
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, neg_zero, zero_div,
    Real.exp_zero]
  have hp : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.mpr (by positivity)
  have hsq : Real.sqrt (2 * Real.pi) ^ 2 = 2 * Real.pi := Real.sq_sqrt (by positivity)
  rw [show 2 / Real.pi = (2 * (1 / Real.sqrt (2 * Real.pi))) ^ 2 by
    rw [mul_pow, div_pow, hsq]; field_simp]
  exact Real.sqrt_sq (by positivity)

lemma bprof_tendsto : Tendsto brownianProfile (𝓝[>] 0) (𝓝 (brownianProfile 0)) := by
  have hslope := (g_cdf_deriv 0).tendsto_slope_zero_right
  simp only [zero_add, smul_eq_mul, cdf_zero] at hslope
  have hq : Tendsto (fun z => (stdNormalCdf z - 1 / 2) / z) (𝓝[>] 0) (𝓝 (stdNormalPdf 0)) :=
    hslope.congr (fun z => (div_eq_inv_mul _ _).symm)
  have hp : Tendsto stdNormalPdf (𝓝[>] 0) (𝓝 (stdNormalPdf 0)) :=
    (g_pdf_cont.tendsto 0).mono_left nhdsWithin_le_nhds
  have hm : Tendsto (fun z => z * (1 - stdNormalCdf z)) (𝓝[>] 0) (𝓝 (0 * (1 - stdNormalCdf 0))) :=
    (((continuous_id.mul (continuous_const.sub cdf_cont)).tendsto 0)).mono_left nhdsWithin_le_nhds
  have hall := (hp.sub hm).add hq
  rw [zero_mul, sub_zero, ← two_mul, ← bprof_zero] at hall
  refine hall.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with z hz
  unfold brownianProfile
  rw [if_neg (ne_of_gt hz)]

theorem brownian_comparison' (T ℓ : ℝ) (hT : 0 < T) (hℓ0 : 0 ≤ ℓ) (hℓ1 : ℓ ≤ 1) :
    expectedMaxExcess T ℓ ≤ Real.sqrt T * brownianProfile (ℓ * Real.sqrt T) := by
  rcases hℓ0.lt_or_eq with hℓ | hℓ
  · exact emx_le_pos T ℓ hT hℓ hℓ1
  subst hℓ
  rw [zero_mul]
  have hs : 0 < Real.sqrt T := Real.sqrt_pos.mpr hT
  have hz : Tendsto (fun l : ℝ => l * Real.sqrt T) (𝓝[>] 0) (𝓝[>] 0) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · have : Tendsto (fun l : ℝ => l * Real.sqrt T) (𝓝 0) (𝓝 (0 * Real.sqrt T)) :=
        tendsto_id.mul_const _
      rw [zero_mul] at this
      exact this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with l hl
      exact mul_pos hl hs
  have hR : Tendsto (fun l : ℝ => Real.sqrt T * brownianProfile (l * Real.sqrt T) + l * T)
      (𝓝[>] 0) (𝓝 (Real.sqrt T * brownianProfile 0 + 0 * T)) :=
    ((bprof_tendsto.comp hz).const_mul _).add
      ((tendsto_id.mul_const T).mono_left nhdsWithin_le_nhds)
  rw [zero_mul, add_zero] at hR
  refine ge_of_tendsto hR ?_
  filter_upwards [Ioo_mem_nhdsGT (show (0:ℝ) < 1 by norm_num)] with l hl
  have h1 := emx_le_pos T l hT hl.1 hl.2.le
  have h2 := Wf_lip T (1 - l) 1 hT.le (by linarith [hl.2]) (by linarith [hl.1])
  have e0 : expectedMaxExcess T 0 = Wf T 1 := by
    unfold expectedMaxExcess Wf; rw [sub_zero]
  have e1 : expectedMaxExcess T l = Wf T (1 - l) := rfl
  rw [e0]
  have : (1 - (1 - l)) * T = l * T := by ring
  linarith

end LostSalesRQ

open LostSalesRQ in
theorem solution (T ℓ : ℝ) (hT : 0 < T) (hℓ0 : 0 ≤ ℓ) (hℓ1 : ℓ ≤ 1) :
    expectedMaxExcess T ℓ ≤ Real.sqrt T * brownianProfile (ℓ * Real.sqrt T) :=
  brownian_comparison' T ℓ hT hℓ0 hℓ1
