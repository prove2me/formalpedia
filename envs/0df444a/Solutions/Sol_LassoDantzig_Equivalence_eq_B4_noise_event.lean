-- Prove2me | solution 1 for LassoDantzig.Equivalence.eq_B4_noise_event
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T04:42:59.919066+00:00
-- url     : https://prove2.me/submissions/d319588b-cbab-42e4-b224-4bdcd4d000ed

import Mathlib
import Definitions.Def_LassoDantzig_Equivalence_Model

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LassoDantzig.Equivalence

lemma aux_ldB4_t1 {v : ℝ≥0} (hv : v ≠ 0) {c : ℝ} (hc : 0 ≤ c) :
    gaussianReal 0 v (Set.Ioi c) ≤
      ENNReal.ofReal (Real.exp (-c ^ 2 / (2 * v))) * gaussianReal 0 v (Set.Ioi 0) := by
  have h1 : gaussianReal 0 v (Set.Ioi c) = gaussianReal (0 - c) v (Set.Ioi 0) := by
    rw [← gaussianReal_map_sub_const c, Measure.map_apply (by fun_prop) measurableSet_Ioi]
    congr 1
    ext x; simp
  rw [h1, gaussianReal_apply _ hv, gaussianReal_apply _ hv, ← lintegral_const_mul _
    (measurable_gaussianPDF _ _)]
  refine setLIntegral_mono (by fun_prop) ?_
  intro x hx
  simp only [Set.mem_Ioi] at hx
  simp only [gaussianPDF, gaussianPDFReal]
  rw [← ENNReal.ofReal_mul (Real.exp_pos _).le]
  apply ENNReal.ofReal_le_ofReal
  rw [mul_left_comm]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hv' : (0 : ℝ) < v := by positivity
  rw [← add_div, div_le_div_iff_of_pos_right (by positivity)]
  nlinarith [mul_nonneg hx.le hc]

lemma aux_ldB4_t2 {v : ℝ≥0} (hv : v ≠ 0) {c : ℝ} (hc : 0 ≤ c) :
    gaussianReal 0 v {t | c < |t|} ≤ ENNReal.ofReal (Real.exp (-c ^ 2 / (2 * v))) := by
  have hsymm : (gaussianReal 0 v).map (fun x => -x) = gaussianReal 0 v := by
    rw [gaussianReal_map_neg, neg_zero]
  have hneg : ∀ a : ℝ, gaussianReal 0 v (Set.Iio (-a)) = gaussianReal 0 v (Set.Ioi a) := by
    intro a
    conv_lhs => rw [← hsymm]
    rw [Measure.map_apply (by fun_prop) measurableSet_Iio]
    congr 1
    ext x; simp
  have hset : {t : ℝ | c < |t|} = Set.Ioi c ∪ Set.Iio (-c) := by
    ext t; simp [lt_abs, lt_neg]
  set e := ENNReal.ofReal (Real.exp (-c ^ 2 / (2 * v)))
  calc gaussianReal 0 v {t | c < |t|}
      ≤ gaussianReal 0 v (Set.Ioi c) + gaussianReal 0 v (Set.Iio (-c)) := by
        rw [hset]; exact measure_union_le _ _
    _ = gaussianReal 0 v (Set.Ioi c) + gaussianReal 0 v (Set.Ioi c) := by rw [hneg]
    _ ≤ e * gaussianReal 0 v (Set.Ioi 0) + e * gaussianReal 0 v (Set.Ioi 0) := by
        gcongr <;> exact aux_ldB4_t1 hv hc
    _ = e * (gaussianReal 0 v (Set.Ioi 0) + gaussianReal 0 v (Set.Iio 0)) := by
        have := hneg 0
        rw [neg_zero] at this
        rw [this, mul_add]
    _ = e * gaussianReal 0 v (Set.Ioi 0 ∪ Set.Iio 0) := by
        rw [measure_union _ measurableSet_Iio]
        rw [Set.disjoint_left]; intro x h1 h2; simp at h1 h2; linarith
    _ ≤ e * 1 := by gcongr; exact prob_le_one
    _ = e := mul_one e

lemma aux_ldB4_s1 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] {ι : Type*}
    (W : ι → Ω → ℝ) (hWm : ∀ i, Measurable (W i)) (hind : iIndepFun W P) (v : ℝ≥0)
    (hlaw : ∀ i, P.map (W i) = gaussianReal 0 v) (a : ι → ℝ) (s : Finset ι) :
    P.map (fun ω => ∑ i ∈ s, a i * W i ω) =
      gaussianReal 0 (∑ i ∈ s, (NNReal.mk (a i ^ 2) (sq_nonneg _)) * v) := by
  classical
  set Y : ι → Ω → ℝ := fun i ω => a i * W i ω with hYdef
  have hYm : ∀ i, Measurable (Y i) := fun i => measurable_const.mul (hWm i)
  have hY : iIndepFun Y P :=
    hind.comp (fun i x => a i * x) (fun i => measurable_const.mul measurable_id)
  have hYlaw : ∀ i, P.map (Y i) = gaussianReal 0 ((NNReal.mk (a i ^ 2) (sq_nonneg _)) * v) := by
    intro i
    have : Y i = (fun x => a i * x) ∘ W i := rfl
    rw [this, ← Measure.map_map (by fun_prop) (hWm i), hlaw i, gaussianReal_map_const_mul,
      mul_zero]
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty, Measure.map_const, measure_univ, one_smul]
    rw [gaussianReal_zero_var]
  | insert b s hb ih =>
    have hfun : (fun ω => ∑ i ∈ insert b s, a i * W i ω) = (∑ j ∈ s, Y j) + Y b := by
      ext ω
      simp [Finset.sum_insert hb, Finset.sum_apply, Y, add_comm]
    have hfun2 : (∑ j ∈ s, Y j) = fun ω => ∑ i ∈ s, a i * W i ω := by
      ext ω; simp [Finset.sum_apply, Y]
    rw [hfun, Finset.sum_insert hb, add_comm ((NNReal.mk (a b ^ 2) (sq_nonneg _)) * v),
      ← add_zero (0 : ℝ)]
    refine gaussianReal_add_gaussianReal_of_indepFun
      (hY.indepFun_finsetSum_of_notMem hYm hb) ?_ (hYlaw b)
    rw [hfun2, ih]

end LassoDantzig.Equivalence

open LassoDantzig.Equivalence

theorem solution {n M : ℕ} (hn : 1 ≤ n) (hM : 2 ≤ M)
    (X : Matrix (Fin n) (Fin M) ℝ) (hX : ∀ j, colNorm X j ≠ 0)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (W : Fin n → Ω → ℝ) (σ : ℝ) (hσ : 0 < σ) (hWm : ∀ i, Measurable (W i))
    (hWind : iIndepFun W P) (hWlaw : ∀ i, P.map (W i) = gaussianReal 0 (σ ^ 2).toNNReal)
    (A : ℝ) (hA : 0 < A) (r : ℝ) (hr : r = A * σ * Real.sqrt (Real.log M / n)) :
    P {ω | ¬ NoiseEventHalf X r (fun i => W i ω)} ≤
      ENNReal.ofReal ((M : ℝ) ^ (1 - A ^ 2 / 8)) := by
  set v : ℝ≥0 := (σ ^ 2).toNNReal with hvdef
  have hv : v ≠ 0 := by
    rw [hvdef]; simp only [ne_eq, Real.toNNReal_eq_zero, not_le]; positivity
  have hvr : (v : ℝ) = σ ^ 2 := by rw [hvdef, Real.coe_toNNReal _ (by positivity)]
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hMpos : (0 : ℝ) < M := by exact_mod_cast (by omega : 0 < M)
  have hlogM : 0 ≤ Real.log M := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ M))
  have hr0 : 0 ≤ r := by rw [hr]; positivity
  have hr2 : r ^ 2 = A ^ 2 * σ ^ 2 * (Real.log M / n) := by
    rw [hr, mul_pow, mul_pow, Real.sq_sqrt (by positivity)]
  set S : Fin M → Ω → ℝ := fun j ω => ∑ i, X i j * W i ω with hSdef
  set V : Fin M → ℝ≥0 := fun j => ∑ i, NNReal.mk (X i j ^ 2) (sq_nonneg _) * v with hVdef
  have hlaw : ∀ j, P.map (S j) = gaussianReal 0 (V j) := fun j =>
    aux_ldB4_s1 P W hWm hWind v hWlaw (fun i => X i j) Finset.univ
  have hcn : ∀ j, colNorm X j ^ 2 = (1 / (n : ℝ)) * ∑ i, X i j ^ 2 := by
    intro j
    unfold colNorm empNorm
    rw [Real.sq_sqrt (by positivity)]
  have hcnpos : ∀ j, 0 < colNorm X j := by
    intro j
    have : 0 ≤ colNorm X j := Real.sqrt_nonneg _
    exact lt_of_le_of_ne this (hX j).symm
  have hVr : ∀ j, (V j : ℝ) = σ ^ 2 * (n * colNorm X j ^ 2) := by
    intro j
    rw [hcn j, hVdef]
    simp only [NNReal.coe_sum, NNReal.coe_mul, NNReal.coe_mk, hvr]
    field_simp
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun _ _ => mul_comm _ _)
  have hVne : ∀ j, V j ≠ 0 := by
    intro j h
    have h' := hVr j
    rw [h, NNReal.coe_zero] at h'
    have := hcnpos j
    have : 0 < σ ^ 2 * (n * colNorm X j ^ 2) := by positivity
    linarith
  set c : Fin M → ℝ := fun j => n * r * colNorm X j / 2 with hcdef
  have hc0 : ∀ j, 0 ≤ c j := fun j => by
    have := hcnpos j
    rw [hcdef]; positivity
  have hexp : ∀ j, Real.exp (-c j ^ 2 / (2 * V j)) = (M : ℝ) ^ (-(A ^ 2 / 8)) := by
    intro j
    rw [Real.rpow_def_of_pos hMpos]
    congr 1
    rw [hVr j, hcdef]
    have := hcnpos j
    have hcn0 : colNorm X j ≠ 0 := hX j
    have hn0 : (n : ℝ) ≠ 0 := hnpos.ne'
    have hσ0 : σ ≠ 0 := hσ.ne'
    simp only
    rw [show -(↑n * r * colNorm X j / 2) ^ 2 = -(↑n ^ 2 * r ^ 2 * colNorm X j ^ 2 / 4) by ring,
      hr2]
    field_simp
    ring
  have hsub : {ω | ¬ NoiseEventHalf X r (fun i => W i ω)} ⊆
      ⋃ j, S j ⁻¹' {t | c j < |t|} := by
    intro ω hω
    simp only [Set.mem_ofPred_eq, NoiseEventHalf, not_forall, not_le] at hω
    obtain ⟨j, hj⟩ := hω
    simp only [Set.mem_iUnion, Set.mem_preimage, Set.mem_ofPred_eq]
    refine ⟨j, ?_⟩
    rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 / n)] at hj
    rw [hcdef, hSdef]
    simp only
    have : n * r * colNorm X j / 2 = (n / 2) * (r * colNorm X j) := by ring
    rw [this]
    calc (n / 2) * (r * colNorm X j) < (n / 2) * (2 * (1 / n * |∑ i, X i j * W i ω|)) := by
          gcongr
      _ = |∑ i, X i j * W i ω| := by field_simp
  have hSm : ∀ j, Measurable (S j) := by
    intro j
    rw [hSdef]
    exact Finset.measurable_sum _ (fun i _ => measurable_const.mul (hWm i))
  calc P {ω | ¬ NoiseEventHalf X r (fun i => W i ω)}
      ≤ P (⋃ j, S j ⁻¹' {t | c j < |t|}) := measure_mono hsub
    _ ≤ ∑ j, P (S j ⁻¹' {t | c j < |t|}) := measure_iUnion_fintype_le _ _
    _ ≤ ∑ j : Fin M, ENNReal.ofReal ((M : ℝ) ^ (-(A ^ 2 / 8))) := by
        gcongr with j
        calc P (S j ⁻¹' {t | c j < |t|}) = (P.map (S j)) {t | c j < |t|} := by
              rw [Measure.map_apply (hSm j)]
              exact measurableSet_lt measurable_const measurable_abs
          _ = gaussianReal 0 (V j) {t | c j < |t|} := by rw [hlaw j]
          _ ≤ ENNReal.ofReal (Real.exp (-c j ^ 2 / (2 * V j))) := aux_ldB4_t2 (hVne j) (hc0 j)
          _ = ENNReal.ofReal ((M : ℝ) ^ (-(A ^ 2 / 8))) := by rw [hexp j]
    _ = ENNReal.ofReal ((M : ℝ) ^ (1 - A ^ 2 / 8)) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        rw [show (M : ℝ≥0∞) = ENNReal.ofReal (M : ℝ) by simp,
          ← ENNReal.ofReal_mul hMpos.le]
        congr 1
        rw [sub_eq_add_neg, Real.rpow_add hMpos, Real.rpow_one]
