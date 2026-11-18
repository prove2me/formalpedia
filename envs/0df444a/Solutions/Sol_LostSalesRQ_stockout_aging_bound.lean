-- Prove2me | solution 1 for LostSalesRQ.stockout_aging_bound
-- status  : ACCEPTED   (prove)
-- author  : @Ming Hu
-- created : 2026-11-17T22:49:23.143051+00:00
-- url     : https://prove2.me/submissions/818afeee-d6e1-4393-b389-97e2f01e525f

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
import Theorems.Thm_LostSalesRQ_penalty_calibration
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Probability.CDF

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

lemma agingSet_bdd (η T : ℝ) (hη : 0 ≤ η) :
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

lemma agingRateSup_mono (η μ T : ℝ) (hη : 0 ≤ η) (hμT : μ ≤ T) :
    agingRateSup μ η ≤ agingRateSup T η := by
  unfold agingRateSup
  apply csSup_le_csSup (agingSet_bdd η T hη)
  · exact ⟨0, 0, fun i => i.elim0, fun a _ _ => a.elim0, fun i => i.elim0, by simp⟩
  · rintro x ⟨m, τ, hm, hτ, rfl⟩
    exact ⟨m, τ, hm, fun i => ⟨(hτ i).1, (hτ i).2.trans hμT⟩, rfl⟩

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

lemma rank_partial_le (T η P : ℝ) (hT : 0 ≤ T) (hη : 1 ≤ η) (hP : ∀ n, poisMass T n ≤ P)
    (l : ℕ) :
    ∑ n ∈ Finset.range l, (η * poisMass T n - poisCdf T n) ≤
        η * ∑ n ∈ Finset.range l, poisMass T n ∧
      ∑ n ∈ Finset.range l, (η * poisMass T n - poisCdf T n) ≤ η ^ 2 * P := by
  have hP0 : 0 ≤ P := le_trans (d2_pm_nonneg T hT 0) (hP 0)
  have hη0 : 0 ≤ η := by linarith
  induction l with
  | zero => simp only [Finset.range_zero, Finset.sum_empty, mul_zero, le_refl, true_and]; positivity
  | succ l ih =>
    obtain ⟨ih1, ih2⟩ := ih
    have hF : poisCdf T l = ∑ n ∈ Finset.range l, poisMass T n + poisMass T l := by
      unfold poisCdf; rw [Finset.sum_range_succ]
    rw [Finset.sum_range_succ, Finset.sum_range_succ]
    have hA : 0 ≤ ∑ n ∈ Finset.range l, poisMass T n :=
      Finset.sum_nonneg (fun n _ => d2_pm_nonneg T hT n)
    have hp : 0 ≤ poisMass T l := d2_pm_nonneg T hT l
    have hpP := hP l
    by_cases hcase : η * poisMass T l ≤ poisCdf T l
    · constructor
      · nlinarith
      · nlinarith
    · push Not at hcase
      constructor
      · nlinarith
      · have h1 : η * poisCdf T l ≤ η * (η * poisMass T l) :=
          mul_le_mul_of_nonneg_left hcase.le hη0
        have h2 : η * (η * poisMass T l) ≤ η ^ 2 * P := by
          rw [← mul_assoc, ← sq]; exact mul_le_mul_of_nonneg_left hpP (sq_nonneg η)
        nlinarith

lemma rankBound_ge (T η P : ℝ) (hT : 0 ≤ T) (hη : 1 ≤ η) (hP : ∀ n, poisMass T n ≤ P) :
    η - η ^ 2 * P ≤ rankBound T η := by
  unfold rankBound
  apply le_ciInf
  intro l
  rw [rank_V]
  linarith [(rank_partial_le T η P hT hη hP l).2]

lemma pm_mul_sqrt_le (T : ℝ) (hT : 0 ≤ T) (n : ℕ) (hn : 1 ≤ n) :
    poisMass T n * Real.sqrt (2 * Real.pi * n) ≤ 1 := by
  have hn0 : (0:ℝ) < n := by exact_mod_cast hn
  have hst := Stirling.le_factorial_stirling n
  have hs : 0 < Real.sqrt (2 * Real.pi * n) := Real.sqrt_pos.mpr (by positivity)
  have hA : 0 < ((n:ℝ) / Real.exp 1) ^ n := by positivity
  have hfac : (0:ℝ) < n.factorial := by positivity
  have hy : T * (Real.exp 1 / n) ≤ Real.exp (T / n) := by
    have h1 := Real.add_one_le_exp (T / n - 1)
    have h2 : Real.exp (T / n) = Real.exp (T / n - 1) * Real.exp 1 := by
      rw [← Real.exp_add]; ring_nf
    have he : 0 < Real.exp 1 := Real.exp_pos 1
    have h3 : T * (Real.exp 1 / n) = (T / n) * Real.exp 1 := by ring
    rw [h2, h3]
    exact mul_le_mul_of_nonneg_right (by linarith) he.le
  have hpow : (T * (Real.exp 1 / n)) ^ n ≤ Real.exp T := by
    calc (T * (Real.exp 1 / n)) ^ n ≤ (Real.exp (T / n)) ^ n :=
          pow_le_pow_left₀ (by positivity) hy n
      _ = Real.exp T := by rw [← Real.exp_nat_mul]; congr 1; field_simp
  have hTn : T ^ n = (T * (Real.exp 1 / n)) ^ n * ((n:ℝ) / Real.exp 1) ^ n := by
    rw [← mul_pow]; congr 1; field_simp
  have hkey : T ^ n ≤ Real.exp T * ((n:ℝ) / Real.exp 1) ^ n := by
    rw [hTn]; exact mul_le_mul_of_nonneg_right hpow hA.le
  unfold poisMass
  rw [div_mul_eq_mul_div, div_le_one hfac]
  have he : Real.exp (-T) * Real.exp T = 1 := by rw [← Real.exp_add]; simp
  calc Real.exp (-T) * T ^ n * Real.sqrt (2 * Real.pi * n)
      ≤ Real.exp (-T) * (Real.exp T * ((n:ℝ) / Real.exp 1) ^ n) * Real.sqrt (2 * Real.pi * n) := by
        gcongr
    _ = Real.sqrt (2 * Real.pi * n) * ((n:ℝ) / Real.exp 1) ^ n := by
        rw [← mul_assoc, he, one_mul, mul_comm]
    _ ≤ n.factorial := hst

lemma pm_small (ε : ℝ) (hε : 0 < ε) : ∃ T₀ : ℝ, ∀ T ≥ T₀, ∀ n : ℕ, poisMass T n ≤ ε := by
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / ε ^ 2)
  have hev : ∀ᶠ T in atTop, ∀ n ∈ Finset.range (N + 1), poisMass T n ≤ ε := by
    rw [Filter.eventually_all_finset]
    intro n _
    have h := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero n).div_const (n.factorial : ℝ)
    rw [zero_div] at h
    filter_upwards [(tendsto_order.1 h).2 ε hε] with T hT
    unfold poisMass
    have : Real.exp (-T) * T ^ n / (n.factorial : ℝ) = T ^ n * Real.exp (-T) / (n.factorial : ℝ) := by
      ring
    rw [this]; exact hT.le
  obtain ⟨T₁, hT₁⟩ := eventually_atTop.1 hev
  refine ⟨max T₁ 0, fun T hT n => ?_⟩
  have hT0 : 0 ≤ T := le_trans (le_max_right _ _) hT
  by_cases hnN : n ≤ N
  · exact hT₁ T (le_trans (le_max_left _ _) hT) n (Finset.mem_range.mpr (by omega))
  · push Not at hnN
    have hn1 : 1 ≤ n := by omega
    have hs := pm_mul_sqrt_le T hT0 n hn1
    have hp := d2_pm_nonneg T hT0 n
    have hn0 : (0:ℝ) < n := by exact_mod_cast hn1
    have hsq : Real.sqrt (2 * Real.pi * n) ^ 2 = 2 * Real.pi * n := Real.sq_sqrt (by positivity)
    have h1 : poisMass T n ^ 2 * (2 * Real.pi * n) ≤ 1 := by
      rw [← hsq, ← mul_pow]
      have : 0 ≤ poisMass T n * Real.sqrt (2 * Real.pi * n) := by positivity
      nlinarith
    have hpi : (1:ℝ) ≤ 2 * Real.pi := by nlinarith [Real.two_le_pi]
    have h2 : poisMass T n ^ 2 * n ≤ 1 := by
      have : poisMass T n ^ 2 * n ≤ poisMass T n ^ 2 * (2 * Real.pi * n) := by
        apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
        nlinarith
      linarith
    have hNn : (N:ℝ) < n := by exact_mod_cast hnN
    have h3 : 1 < (n:ℝ) * ε ^ 2 := by
      have := lt_trans hN hNn
      rw [div_lt_iff₀ (by positivity)] at this
      exact this
    by_contra hc
    push Not at hc
    have h4 : ε ^ 2 < poisMass T n ^ 2 := pow_lt_pow_left₀ hc hε.le two_ne_zero
    nlinarith

lemma pade_bound (z : ℝ) (hz : 0 ≤ z) : Real.exp (-z) * (2 * z + 6) ≤ z ^ 2 - 4 * z + 6 := by
  have h5 : 1 + z + z ^ 2 / 2 + z ^ 3 / 6 + z ^ 4 / 24 ≤ Real.exp z := by
    have := Real.sum_le_exp_of_nonneg hz 5
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at this
    norm_num at this
    linarith
  have hq : 0 < z ^ 2 - 4 * z + 6 := by nlinarith [sq_nonneg (z - 2)]
  have hprod : 2 * z + 6 ≤ (z ^ 2 - 4 * z + 6) * Real.exp z := by
    have hid : (z ^ 2 - 4 * z + 6) * (1 + z + z ^ 2 / 2 + z ^ 3 / 6 + z ^ 4 / 24) =
        6 + 2 * z + z ^ 4 / 12 + z ^ 6 / 24 := by ring
    nlinarith [mul_le_mul_of_nonneg_left h5 hq.le, pow_nonneg hz 4, pow_nonneg hz 6]
  have he : Real.exp (-z) * Real.exp z = 1 := by rw [← Real.exp_add]; simp
  calc Real.exp (-z) * (2 * z + 6) ≤ Real.exp (-z) * ((z ^ 2 - 4 * z + 6) * Real.exp z) :=
        mul_le_mul_of_nonneg_left hprod (Real.exp_pos _).le
    _ = z ^ 2 - 4 * z + 6 := by rw [mul_comm (z ^ 2 - 4 * z + 6), ← mul_assoc, he, one_mul]

end LostSalesRQ

open LostSalesRQ in
theorem solution (μ η : ℝ) (hμ : 0 ≤ μ) (hη : 1 ≤ η) :
    agingRateSup μ η ≤ η ^ 2 / 2 - η / 3 := by
  have hη0 : 0 < η := by linarith
  have h32 : 0 < 3 * η - 2 := by linarith
  set f := 1 - 1 / η with hfdef
  set lam := 6 / (3 * η - 2) with hlamdef
  have hlam : 0 < lam := by positivity
  have hf : 0 ≤ f := by rw [hfdef, sub_nonneg, div_le_one hη0]; exact hη
  have hid : (1 - lam * f) * (2 * lam + 6) = lam ^ 2 - 4 * lam + 6 := by
    rw [hfdef, hlamdef]; field_simp; ring
  have hkey : Real.exp (-lam) ≤ 1 - lam * f := by
    have h1 := pade_bound lam hlam.le
    rw [← hid] at h1
    exact le_of_mul_le_mul_right h1 (by positivity)
  have hr : 0 < 1 - lam * f := lt_of_lt_of_le (Real.exp_pos _) hkey
  have hηlam : η * (1 / lam) = η ^ 2 / 2 - η / 3 := by
    rw [hlamdef]; field_simp; ring
  apply le_of_forall_sub_le
  intro ε hε
  obtain ⟨T₀, hT₀⟩ := pm_small (ε / η ^ 2) (by positivity)
  set T := max μ (max T₀ 0) with hTdef
  have hT0 : 0 ≤ T := le_trans (le_max_right _ _) (le_max_right _ _)
  have hμT : μ ≤ T := le_max_left _ _
  have hTT₀ : T₀ ≤ T := le_trans (le_max_left _ _) (le_max_right _ _)
  have h1 := agingRateSup_mono η μ T hη0.le hμT
  have h2 := (penalty_calibration T hT0).1 η hη
  have h3 := rankBound_ge T η (ε / η ^ 2) hT0 hη (fun n => hT₀ T hTT₀ n)
  have h4 : expectedMaxExcess T (1 / η) ≤ 1 / lam :=
    expectedMaxExcess_le T f lam hf hlam hr hkey
  unfold calibratedPenalty at h2
  have h5 : η ^ 2 * (ε / η ^ 2) = ε := by field_simp
  have h6 : η * expectedMaxExcess T (1 / η) ≤ η * (1 / lam) := mul_le_mul_of_nonneg_left h4 hη0.le
  nlinarith
