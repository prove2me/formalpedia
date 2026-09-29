-- Prove2me | solution 1 for LassoDantzig.Oracle.eq_B4_noise_event
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T03:49:40.31253+00:00
-- url     : https://prove2.me/submissions/e120e56f-847c-4c85-acda-1399eca3b4de

import Mathlib
import Definitions.Def_LassoDantzig_Oracle_Model

open MeasureTheory ProbabilityTheory

namespace LassoDantzig.Oracle

lemma aux_OB4_pdf_le (v : NNReal) (m x : ℝ) (h : 0 ≤ (x - m) * m) :
    gaussianPDF 0 v x ≤ ENNReal.ofReal (Real.exp (-m ^ 2 / (2 * v))) * gaussianPDF m v x := by
  simp only [gaussianPDF, gaussianPDFReal]
  rw [← ENNReal.ofReal_mul (Real.exp_pos _).le]
  apply ENNReal.ofReal_le_ofReal
  rw [mul_left_comm]
  apply mul_le_mul_of_nonneg_left _ (inv_nonneg.2 (Real.sqrt_nonneg _))
  rw [← Real.exp_add]
  apply Real.exp_le_exp.2
  rcases eq_or_lt_of_le (NNReal.coe_nonneg v) with hv | hv
  · rw [← hv]; simp
  rw [← add_div, div_le_div_iff_of_pos_right (by positivity)]
  nlinarith

lemma aux_OB4_tail (v : NNReal) (hv : v ≠ 0) (t : ℝ) (ht : 0 ≤ t) :
    gaussianReal 0 v {x | t < |x|} ≤ ENNReal.ofReal (Real.exp (-t ^ 2 / (2 * v))) := by
  set c := ENNReal.ofReal (Real.exp (-t ^ 2 / (2 * v))) with hc
  have hset : {x : ℝ | t < |x|} = Set.Ioi t ∪ Set.Iio (-t) := by
    ext x; simp only [Set.mem_union, Set.mem_Ioi, Set.mem_Iio, lt_abs]
    constructor <;> rintro (h | h) <;> [left; right; left; right] <;> linarith
  have h1 : gaussianReal 0 v (Set.Ioi t) ≤ c * gaussianReal t v (Set.Ioi t) := by
    rw [gaussianReal_apply _ hv, gaussianReal_apply _ hv,
      ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine setLIntegral_mono' measurableSet_Ioi (fun x hx => ?_)
    have := aux_OB4_pdf_le v t x (mul_nonneg (by simp at hx; linarith) ht)
    exact this
  have h2 : gaussianReal 0 v (Set.Iio (-t)) ≤ c * gaussianReal (-t) v (Set.Iio (-t)) := by
    rw [gaussianReal_apply _ hv, gaussianReal_apply _ hv,
      ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine setLIntegral_mono' measurableSet_Iio (fun x hx => ?_)
    have := aux_OB4_pdf_le v (-t) x
      (mul_nonneg_of_nonpos_of_nonpos (by simp at hx; linarith) (by linarith))
    rwa [neg_sq] at this
  have h3 : gaussianReal t v (Set.Ioi t) = gaussianReal 0 v (Set.Ioi 0) := by
    have := gaussianReal_map_add_const (μ := 0) (v := v) t
    rw [zero_add] at this
    rw [← this, Measure.map_apply (measurable_add_const t) measurableSet_Ioi]
    congr 1; ext x; simp
  have h4 : gaussianReal (-t) v (Set.Iio (-t)) = gaussianReal 0 v (Set.Iio 0) := by
    have := gaussianReal_map_add_const (μ := 0) (v := v) (-t)
    rw [zero_add] at this
    rw [← this, Measure.map_apply (measurable_add_const (-t)) measurableSet_Iio]
    congr 1; ext x; simp
  have h5 : gaussianReal 0 v (Set.Ioi 0) + gaussianReal 0 v (Set.Iio 0) ≤ 1 := by
    rw [← measure_union _ measurableSet_Iio]
    · exact prob_le_one
    · exact Set.disjoint_left.2 (fun x hx hx' => by simp at hx hx'; linarith)
  rw [hset]
  calc gaussianReal 0 v (Set.Ioi t ∪ Set.Iio (-t))
      ≤ gaussianReal 0 v (Set.Ioi t) + gaussianReal 0 v (Set.Iio (-t)) := measure_union_le _ _
    _ ≤ c * gaussianReal 0 v (Set.Ioi 0) + c * gaussianReal 0 v (Set.Iio 0) := by
        rw [← h3, ← h4]; exact add_le_add h1 h2
    _ = c * (gaussianReal 0 v (Set.Ioi 0) + gaussianReal 0 v (Set.Iio 0)) := by rw [mul_add]
    _ ≤ c * 1 := by gcongr
    _ = c := mul_one c

lemma aux_OB4_law {n M : ℕ} (hn : 1 ≤ n)
    (X : Matrix (Fin n) (Fin M) ℝ)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (W : Fin n → Ω → ℝ) (σ : ℝ) (hWm : ∀ i, Measurable (W i))
    (hWind : iIndepFun W P) (hWlaw : ∀ i, P.map (W i) = gaussianReal 0 (σ ^ 2).toNNReal)
    (j : Fin M) :
    P.map (noiseCorr X W j) =
      gaussianReal 0 (σ ^ 2 * (∑ i, X i j ^ 2) / (n : ℝ) ^ 2).toNNReal := by
  have hn' : (0 : ℝ) < n := Nat.cast_pos.2 hn
  set c : Fin n → ℝ := fun i => (1 / (n : ℝ)) * X i j with hc
  have hWG : ∀ i, HasGaussianLaw (W i) P := fun i =>
    (HasLaw.mk (hWm i).aemeasurable (hWlaw i)).hasGaussianLaw
  have hZG : ∀ i, HasGaussianLaw (fun ω => c i * W i ω) P := fun i => by
    simpa [smul_eq_mul] using (hWG i).fun_smul (c i)
  have hZind : iIndepFun (fun i ω => c i * W i ω) P :=
    hWind.comp (fun i x => c i * x) (fun i => measurable_const.mul measurable_id)
  have hYeq : noiseCorr X W j = fun ω => ∑ i, c i * W i ω := by
    funext ω; simp only [noiseCorr, hc, Finset.mul_sum, mul_assoc]
  have hYG : HasGaussianLaw (fun ω => ∑ i, c i * W i ω) P := hZind.hasGaussianLaw_fun_sum hZG
  have hmeanW : ∀ i, ∫ ω, W i ω ∂P = 0 := fun i => by
    calc ∫ ω, W i ω ∂P = ∫ x, x ∂(P.map (W i)) :=
          (integral_map (f := fun x : ℝ => x) (hWm i).aemeasurable aestronglyMeasurable_id).symm
      _ = 0 := by rw [hWlaw i]; exact integral_id_gaussianReal
  have hvarW : ∀ i, Var[W i; P] = σ ^ 2 := fun i => by
    have := variance_map (X := id) (μ := P) (Y := W i) aemeasurable_id (hWm i).aemeasurable
    rw [hWlaw i, variance_id_gaussianReal] at this
    rw [← Function.id_comp (W i), ← this, Real.coe_toNNReal _ (sq_nonneg _)]
  rw [hYeq, hYG.map_eq_gaussianReal]
  congr 1
  · rw [integral_finsetSum _ (fun i _ => (hZG i).integrable)]
    simp [integral_const_mul, hmeanW]
  · congr 1
    have hsum : (fun ω => ∑ i, c i * W i ω) = ∑ i, (fun ω => c i * W i ω) := by
      funext ω; simp
    rw [hsum, IndepFun.variance_sum (fun i _ => (hZG i).memLp_two)
      (fun i _ k _ hik => hZind.indepFun hik)]
    simp only [variance_const_mul, hvarW, hc]
    rw [Finset.mul_sum, Finset.sum_div]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    field_simp

end LassoDantzig.Oracle

open LassoDantzig.Oracle

open MeasureTheory ProbabilityTheory

theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {n M : ℕ} (hn : 1 ≤ n) (hM : 2 ≤ M)
    (X : Matrix (Fin n) (Fin M) ℝ) (hcol : ∀ j, colNorm X j ≠ 0)
    (W : Fin n → Ω → ℝ) (σ : ℝ) (hσ : 0 < σ) (hW : GaussianNoise P W σ)
    (A : ℝ) (hA : 2 * Real.sqrt 2 < A) :
    MeasurableSet (noiseEvent X W (tuning n M A σ)) ∧
      P (noiseEvent X W (tuning n M A σ))ᶜ ≤ ENNReal.ofReal ((M : ℝ) ^ (1 - A ^ 2 / 8)) := by
  obtain ⟨hWm, hWind, hWlaw⟩ := hW
  have hn' : (0 : ℝ) < n := Nat.cast_pos.2 hn
  have hM' : (2 : ℝ) ≤ M := by exact_mod_cast hM
  have hMpos : (0 : ℝ) < M := by linarith
  have hlogM : 0 < Real.log M := Real.log_pos (by linarith)
  have hA0 : 0 < A := lt_of_le_of_lt (by positivity) hA
  set r := tuning n M A σ with hr
  have hr0 : 0 ≤ r := by rw [hr, tuning]; positivity
  have hr2 : r ^ 2 = A ^ 2 * σ ^ 2 * (Real.log M / n) := by
    rw [hr, tuning, mul_pow, mul_pow, Real.sq_sqrt (by positivity)]
  have hYm : ∀ j, Measurable (noiseCorr X W j) := fun j => by
    unfold noiseCorr
    exact measurable_const.mul (Finset.measurable_sum _ (fun i _ => measurable_const.mul (hWm i)))
  set S : Fin M → ℝ := fun j => ∑ i, X i j ^ 2 with hS
  have hSpos : ∀ j, 0 < S j := fun j => by
    have h := hcol j
    simp only [colNorm, empNorm, empSq] at h
    have h0 : 0 ≤ S j := Finset.sum_nonneg (fun i _ => sq_nonneg _)
    rcases eq_or_lt_of_le h0 with h1 | h1
    · exfalso; apply h; rw [show (∑ i, X i j ^ 2) = S j from rfl, ← h1]; simp
    · exact h1
  have hcn2 : ∀ j, colNorm X j ^ 2 = S j / n := fun j => by
    simp only [colNorm, empNorm, empSq]
    rw [Real.sq_sqrt (by have := hSpos j; positivity)]
    simp [hS, div_eq_inv_mul]
  have hcn0 : ∀ j, 0 ≤ colNorm X j := fun j => Real.sqrt_nonneg _
  set e : ℝ := (M : ℝ) ^ (-(A ^ 2 / 8)) with he
  have htail : ∀ j, P {ω | r * colNorm X j < 2 * |noiseCorr X W j ω|} ≤ ENNReal.ofReal e :=
    fun j => by
    have hset : {ω | r * colNorm X j < 2 * |noiseCorr X W j ω|} =
        noiseCorr X W j ⁻¹' {x | r * colNorm X j / 2 < |x|} := by
      ext ω; simp only [Set.mem_preimage, Set.mem_ofPred_eq]
      constructor <;> intro h <;> linarith
    rw [hset, ← Measure.map_apply (hYm j)
      (measurableSet_lt measurable_const continuous_abs.measurable)]
    rw [aux_OB4_law hn X P W σ hWm hWind hWlaw j]
    have hvpos : 0 < σ ^ 2 * (∑ i, X i j ^ 2) / (n : ℝ) ^ 2 := by
      have := hSpos j; simp only [hS] at this; positivity
    have hv : (σ ^ 2 * (∑ i, X i j ^ 2) / (n : ℝ) ^ 2).toNNReal ≠ 0 := by
      rw [Ne, Real.toNNReal_eq_zero, not_le]; exact hvpos
    have := aux_OB4_tail _ hv (r * colNorm X j / 2) (by have := hcn0 j; positivity)
    rw [Real.coe_toNNReal _ hvpos.le] at this
    refine this.trans (le_of_eq ?_)
    congr 1
    rw [he, Real.rpow_def_of_pos hMpos]
    congr 1
    have hSj := hSpos j
    rw [div_pow, mul_pow, hr2, hcn2 j]
    simp only [hS] at hSj ⊢
    field_simp
    ring
  have hsub : (noiseEvent X W r)ᶜ ⊆ ⋃ j, {ω | r * colNorm X j < 2 * |noiseCorr X W j ω|} := by
    intro ω hω
    simp only [noiseEvent, Set.mem_compl_iff, Set.mem_ofPred_eq, not_forall, not_le] at hω
    obtain ⟨j, hj⟩ := hω
    exact Set.mem_iUnion.2 ⟨j, hj⟩
  have hfinal : (M : ℝ) * e = (M : ℝ) ^ (1 - A ^ 2 / 8) := by
    rw [he, sub_eq_add_neg, Real.rpow_add hMpos, Real.rpow_one]
  refine ⟨?_, ?_⟩
  · have : noiseEvent X W r = ⋂ j, {ω | 2 * |noiseCorr X W j ω| ≤ r * colNorm X j} := by
      ext ω; simp [noiseEvent]
    rw [this]
    exact MeasurableSet.iInter (fun j =>
      measurableSet_le (measurable_const.mul ((hYm j).abs)) measurable_const)
  calc P (noiseEvent X W r)ᶜ
      ≤ P (⋃ j, {ω | r * colNorm X j < 2 * |noiseCorr X W j ω|}) := measure_mono hsub
    _ ≤ ∑ j, P {ω | r * colNorm X j < 2 * |noiseCorr X W j ω|} := measure_iUnion_fintype_le _ _
    _ ≤ ∑ _j : Fin M, ENNReal.ofReal e := Finset.sum_le_sum fun j _ => htail j
    _ = ENNReal.ofReal ((M : ℝ) * e) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
          ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
    _ = ENNReal.ofReal ((M : ℝ) ^ (1 - A ^ 2 / 8)) := by rw [hfinal]
