-- Prove2me | solution 1 for LassoDantzig.Dantzig.noise_event_B
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T01:58:10.814005+00:00
-- url     : https://prove2.me/submissions/0c84aafe-37bd-42ae-9a84-9ffe6b007fc9

import Mathlib
import Definitions.Def_LassoDantzig_Dantzig_Model

open MeasureTheory ProbabilityTheory

namespace LassoDantzig.Dantzig

open scoped NNReal ENNReal

lemma aux_nb_pdf_le (m : ℝ) (v : ℝ≥0) (hv : v ≠ 0) (x : ℝ) (hmx : m * x ≤ 0) :
    gaussianPDF m v x ≤ ENNReal.ofReal (Real.exp (-m ^ 2 / (2 * v))) * gaussianPDF 0 v x := by
  rw [gaussianPDF, gaussianPDF, ← ENNReal.ofReal_mul (Real.exp_pos _).le]
  apply ENNReal.ofReal_le_ofReal
  rw [gaussianPDFReal, gaussianPDFReal]
  have hv' : (0 : ℝ) < v := by positivity
  have hK : 0 ≤ (√(2 * Real.pi * v))⁻¹ := by positivity
  rw [mul_left_comm, ← Real.exp_add]
  apply mul_le_mul_of_nonneg_left _ hK
  apply Real.exp_le_exp.mpr
  rw [← add_div, div_le_div_iff_of_pos_right (by positivity)]
  nlinarith

lemma aux_nb_tail (v : ℝ≥0) (hv : v ≠ 0) (c : ℝ) (hc : 0 ≤ c) :
    gaussianReal 0 v {x | c < |x|} ≤ ENNReal.ofReal (Real.exp (-c ^ 2 / (2 * v))) := by
  set e := ENNReal.ofReal (Real.exp (-c ^ 2 / (2 * v)))
  have hsub : {x : ℝ | c < |x|} ⊆ Set.Ioi c ∪ Set.Iio (-c) := by
    intro x hx
    simp only [Set.mem_ofPred_eq] at hx
    rcases lt_abs.mp hx with h | h
    · exact Or.inl h
    · exact Or.inr (by simp; linarith)
  have h1 : gaussianReal 0 v (Set.Ioi c) ≤ e * gaussianReal 0 v (Set.Ioi 0) := by
    have : gaussianReal 0 v (Set.Ioi c) = gaussianReal (0 - c) v (Set.Ioi 0) := by
      rw [← gaussianReal_map_sub_const, Measure.map_apply (by fun_prop) measurableSet_Ioi]
      congr 1
      ext x; simp
    rw [this, gaussianReal_apply _ hv, gaussianReal_apply _ hv, ← lintegral_const_mul _
      (measurable_gaussianPDF _ _)]
    apply setLIntegral_mono (by fun_prop)
    intro x hx
    have := aux_nb_pdf_le (0 - c) v hv x (by simp at hx ⊢; nlinarith)
    simpa [e] using this
  have h2 : gaussianReal 0 v (Set.Iio (-c)) ≤ e * gaussianReal 0 v (Set.Iio 0) := by
    have : gaussianReal 0 v (Set.Iio (-c)) = gaussianReal (0 + c) v (Set.Iio 0) := by
      rw [← gaussianReal_map_add_const, Measure.map_apply (by fun_prop) measurableSet_Iio]
      congr 1
      ext x; simp [lt_neg_iff_add_neg]
    rw [this, gaussianReal_apply _ hv, gaussianReal_apply _ hv, ← lintegral_const_mul _
      (measurable_gaussianPDF _ _)]
    apply setLIntegral_mono (by fun_prop)
    intro x hx
    have := aux_nb_pdf_le (0 + c) v hv x (by simp at hx ⊢; nlinarith)
    simpa [e] using this
  have h3 : gaussianReal 0 v (Set.Ioi 0) + gaussianReal 0 v (Set.Iio 0) ≤ 1 := by
    have hd : Disjoint (Set.Ioi (0:ℝ)) (Set.Iio 0) :=
      Set.disjoint_left.mpr fun x (h1 : 0 < x) (h2 : x < 0) => by linarith
    rw [← measure_union hd measurableSet_Iio]
    exact prob_le_one
  calc gaussianReal 0 v {x | c < |x|}
      ≤ gaussianReal 0 v (Set.Ioi c ∪ Set.Iio (-c)) := measure_mono hsub
    _ ≤ gaussianReal 0 v (Set.Ioi c) + gaussianReal 0 v (Set.Iio (-c)) := measure_union_le _ _
    _ ≤ e * gaussianReal 0 v (Set.Ioi 0) + e * gaussianReal 0 v (Set.Iio 0) := add_le_add h1 h2
    _ = e * (gaussianReal 0 v (Set.Ioi 0) + gaussianReal 0 v (Set.Iio 0)) := by rw [mul_add]
    _ ≤ e * 1 := by gcongr
    _ = e := mul_one e

lemma aux_nb_law {n : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (W : Fin n → Ω → ℝ) (σ : ℝ) (hWm : ∀ i, Measurable (W i)) (hWind : iIndepFun W P)
    (hWlaw : ∀ i, P.map (W i) = gaussianReal 0 (σ ^ 2).toNNReal) (a : Fin n → ℝ) :
    P.map (fun ω => ∑ i, a i * W i ω) = gaussianReal 0 (σ ^ 2 * ∑ i, a i ^ 2).toNNReal := by
  have hL : ∀ i, HasLaw (W i) (gaussianReal 0 (σ ^ 2).toNNReal) P :=
    fun i => ⟨(hWm i).aemeasurable, hWlaw i⟩
  have hY : ∀ i, HasGaussianLaw (fun ω => a i * W i ω) P :=
    fun i => (gaussianReal_const_mul (hL i) (a i)).hasGaussianLaw
  have hind : iIndepFun (fun i ω => a i * W i ω) P :=
    hWind.comp (fun i x => a i * x) (fun i => by fun_prop)
  have hS := hind.hasGaussianLaw_fun_sum hY
  rw [hS.map_eq_gaussianReal]
  congr 1
  · rw [integral_finsetSum _ (fun i _ => (hY i).integrable)]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [integral_const_mul, (hL i).integral_eq, integral_id_gaussianReal, mul_zero]
  · congr 1
    have hfun : (fun ω => ∑ i, a i * W i ω) = ∑ i ∈ Finset.univ, (fun ω => a i * W i ω) := by
      ext ω; simp [Finset.sum_apply]
    rw [hfun, IndepFun.variance_sum (fun i _ => (hY i).memLp_two)
      (fun i _ j _ hij => hind.indepFun hij), Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [variance_const_mul, (hL i).variance_eq, variance_id_gaussianReal,
      Real.coe_toNNReal _ (sq_nonneg σ), mul_comm]


lemma aux_nb_single {n M : ℕ} (hn : 1 ≤ n) (hM : 2 ≤ M)
    (X : Matrix (Fin n) (Fin M) ℝ) (hX : ∀ j, colNorm X j ≠ 0)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (W : Fin n → Ω → ℝ) (σ : ℝ) (hσ : 0 < σ) (hWm : ∀ i, Measurable (W i))
    (hWind : iIndepFun W P) (hWlaw : ∀ i, P.map (W i) = gaussianReal 0 (σ ^ 2).toNNReal)
    (A : ℝ) (hA : 0 < A) (r : ℝ) (hr : r = A * σ * Real.sqrt (Real.log M / n)) (j : Fin M) :
    P {ω | r * colNorm X j < |(1 / (n : ℝ)) * ∑ i, X i j * W i ω|} ≤
      ENNReal.ofReal ((M : ℝ) ^ (-(A ^ 2 / 2))) := by
  set s2 : ℝ := ∑ i, X i j ^ 2 with hs2
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hMpos : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hlogM : 0 ≤ Real.log M := Real.log_nonneg (by exact_mod_cast (show 1 ≤ M by omega))
  have hs2nn : 0 ≤ s2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hs2pos : 0 < s2 := by
    rcases hs2nn.lt_or_eq with h | h
    · exact h
    · exfalso; apply hX j; simp [colNorm, ← hs2, ← h]
  have hr0 : 0 ≤ r := by rw [hr]; positivity
  have hcn0 : 0 ≤ colNorm X j := Real.sqrt_nonneg _
  set c : ℝ := n * r * colNorm X j with hc
  have hc0 : 0 ≤ c := by positivity
  set S : Ω → ℝ := fun ω => ∑ i, X i j * W i ω with hS
  have hSm : Measurable S := by
    rw [hS]; exact Finset.measurable_sum _ fun i _ => (hWm i).const_mul _
  have hset : {ω | r * colNorm X j < |(1 / (n : ℝ)) * ∑ i, X i j * W i ω|} =
      S ⁻¹' {x | c < |x|} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, hS, hc]
    rw [abs_mul, abs_of_pos (by positivity : (0:ℝ) < 1 / n), one_div, ← div_eq_inv_mul,
      lt_div_iff₀ hnpos]
    constructor <;> intro h <;> linarith
  have hmeas : MeasurableSet {x : ℝ | c < |x|} :=
    measurableSet_lt measurable_const measurable_abs
  rw [hset, ← Measure.map_apply hSm hmeas, hS, aux_nb_law P W σ hWm hWind hWlaw (fun i => X i j)]
  have hvpos : 0 < σ ^ 2 * s2 := by positivity
  have hv : (σ ^ 2 * s2).toNNReal ≠ 0 := by
    rw [Ne, Real.toNNReal_eq_zero, not_le]; exact hvpos
  refine (aux_nb_tail _ hv c hc0).trans (le_of_eq ?_)
  congr 1
  rw [Real.coe_toNNReal _ hvpos.le, Real.rpow_def_of_pos hMpos]
  congr 1
  have hr2 : r ^ 2 = A ^ 2 * σ ^ 2 * (Real.log M / n) := by
    rw [hr, mul_pow, mul_pow, Real.sq_sqrt (by positivity)]
  have hcn2 : colNorm X j ^ 2 = 1 / n * s2 := by
    rw [colNorm, Real.sq_sqrt (by positivity)]
  have hc2 : c ^ 2 = n ^ 2 * r ^ 2 * colNorm X j ^ 2 := by rw [hc]; ring
  rw [hc2, hr2, hcn2]
  field_simp

end LassoDantzig.Dantzig

open LassoDantzig.Dantzig
open MeasureTheory ProbabilityTheory

theorem solution {n M : ℕ} (hn : 1 ≤ n) (hM : 2 ≤ M)
    (X : Matrix (Fin n) (Fin M) ℝ) (hX : ∀ j, colNorm X j ≠ 0)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (W : Fin n → Ω → ℝ) (σ : ℝ) (hσ : 0 < σ) (hWm : ∀ i, Measurable (W i))
    (hWind : iIndepFun W P) (hWlaw : ∀ i, P.map (W i) = gaussianReal 0 (σ ^ 2).toNNReal)
    (A : ℝ) (hA : 0 < A) (r : ℝ) (hr : r = A * σ * Real.sqrt (Real.log M / n)) :
    P {ω | ¬ NoiseEvent X r (fun i => W i ω)} ≤
      ENNReal.ofReal ((M : ℝ) ^ (1 - A ^ 2 / 2)) := by
  have hMpos : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hU : {ω | ¬ NoiseEvent X r (fun i => W i ω)} =
      ⋃ j, {ω | r * colNorm X j < |(1 / (n : ℝ)) * ∑ i, X i j * W i ω|} := by
    ext ω
    simp [NoiseEvent, not_forall, not_le]
  rw [hU]
  refine (measure_iUnion_fintype_le _ _).trans ?_
  refine (Finset.sum_le_sum fun j _ =>
    aux_nb_single hn hM X hX P W σ hσ hWm hWind hWlaw A hA r hr j).trans (le_of_eq ?_)
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    show (1 : ℝ) - A ^ 2 / 2 = 1 + (-(A ^ 2 / 2)) by ring, Real.rpow_add hMpos, Real.rpow_one,
    ENNReal.ofReal_mul hMpos.le, ENNReal.ofReal_natCast]
