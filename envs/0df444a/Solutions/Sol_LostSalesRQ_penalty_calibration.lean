-- Prove2me | solution 1 for LostSalesRQ.penalty_calibration
-- status  : ACCEPTED   (prove)
-- author  : @Ming Hu
-- created : 2026-11-17T23:21:03.245714+00:00
-- url     : https://prove2.me/submissions/68e95fc6-6fad-4fff-afc3-9ba219345e36

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

open LostSalesRQ in
theorem solution (μ : ℝ) (hμ : 0 ≤ μ) :
    (∀ η : ℝ, 1 ≤ η → rankBound μ η + agingRateSup μ η = calibratedPenalty μ η) ∧
    ContinuousOn (calibratedPenalty μ) (Set.Ici 1) ∧
    StrictMonoOn (calibratedPenalty μ) (Set.Ici 1) ∧
    Set.BijOn (calibratedPenalty μ) (Set.Ici 1) (Set.Ici 1) :=
  ⟨fun η hη => calibration_identity μ η hμ hη, calibratedPenalty_continuousOn μ hμ,
    calibratedPenalty_strictMonoOn μ hμ, calibratedPenalty_bijOn μ hμ⟩
