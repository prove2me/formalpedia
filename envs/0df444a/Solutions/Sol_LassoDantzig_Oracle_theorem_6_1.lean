-- Prove2me | solution 1 for LassoDantzig.Oracle.theorem_6_1
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T04:01:47.022865+00:00
-- url     : https://prove2.me/submissions/374362b4-9e79-44c3-bb61-fd1b38a6cf21

import Mathlib
import Definitions.Def_LassoDantzig_Oracle_Model

open MeasureTheory ProbabilityTheory

namespace LassoDantzig.Oracle

open scoped NNReal ENNReal

/-! ### Gaussian tail and the probability of the noise event -/

lemma aux_t61_pdf_le (m : ℝ) (v : ℝ≥0) (hv : v ≠ 0) (x : ℝ) (hmx : m * x ≤ 0) :
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

lemma aux_t61_tail (v : ℝ≥0) (hv : v ≠ 0) (c : ℝ) (hc : 0 ≤ c) :
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
    have := aux_t61_pdf_le (0 - c) v hv x (by simp at hx ⊢; nlinarith)
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
    have := aux_t61_pdf_le (0 + c) v hv x (by simp at hx ⊢; nlinarith)
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

lemma aux_t61_law {n : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
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

lemma aux_t61_single {n M : ℕ} (hn : 1 ≤ n) (hM : 2 ≤ M)
    (X : Matrix (Fin n) (Fin M) ℝ) (hX : ∀ j, colNorm X j ≠ 0)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (W : Fin n → Ω → ℝ) (σ : ℝ) (hσ : 0 < σ) (hWm : ∀ i, Measurable (W i))
    (hWind : iIndepFun W P) (hWlaw : ∀ i, P.map (W i) = gaussianReal 0 (σ ^ 2).toNNReal)
    (A : ℝ) (hA : 0 < A) (j : Fin M) :
    P {ω | tuning n M A σ * colNorm X j < 2 * |noiseCorr X W j ω|} ≤
      ENNReal.ofReal ((M : ℝ) ^ (-(A ^ 2 / 8))) := by
  set r := tuning n M A σ with hr
  set s2 : ℝ := ∑ i, X i j ^ 2 with hs2
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hMpos : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hlogM : 0 ≤ Real.log M := Real.log_nonneg (by exact_mod_cast (show 1 ≤ M by omega))
  have hs2nn : 0 ≤ s2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hcn2 : colNorm X j ^ 2 = 1 / n * s2 := by
    rw [colNorm, empNorm, empSq, Real.sq_sqrt (by positivity)]
  have hs2pos : 0 < s2 := by
    rcases hs2nn.lt_or_eq with h | h
    · exact h
    · exfalso; apply hX j
      have : colNorm X j ^ 2 = 0 := by rw [hcn2, ← h]; ring
      exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this
  have hr0 : 0 ≤ r := by rw [hr, tuning]; positivity
  have hcn0 : 0 ≤ colNorm X j := Real.sqrt_nonneg _
  set c : ℝ := r * colNorm X j * (n / 2) with hc
  have hc0 : 0 ≤ c := by positivity
  set S : Ω → ℝ := fun ω => ∑ i, X i j * W i ω with hS
  have hSm : Measurable S := by
    rw [hS]; exact Finset.measurable_sum _ fun i _ => (hWm i).const_mul _
  have hset : {ω | r * colNorm X j < 2 * |noiseCorr X W j ω|} =
      S ⁻¹' {x | c < |x|} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, hS, hc, noiseCorr]
    rw [abs_mul, abs_of_pos (by positivity : (0:ℝ) < 1 / n)]
    have e1 : 2 * (1 / (n : ℝ) * |∑ i, X i j * W i ω|) = |∑ i, X i j * W i ω| / (n / 2) := by
      field_simp
    rw [e1, lt_div_iff₀ (by positivity)]
  have hmeas : MeasurableSet {x : ℝ | c < |x|} :=
    measurableSet_lt measurable_const measurable_abs
  rw [hset, ← Measure.map_apply hSm hmeas, hS, aux_t61_law P W σ hWm hWind hWlaw (fun i => X i j)]
  have hvpos : 0 < σ ^ 2 * s2 := by positivity
  have hv : (σ ^ 2 * s2).toNNReal ≠ 0 := by
    rw [Ne, Real.toNNReal_eq_zero, not_le]; exact hvpos
  refine (aux_t61_tail _ hv c hc0).trans (le_of_eq ?_)
  congr 1
  rw [Real.coe_toNNReal _ hvpos.le, Real.rpow_def_of_pos hMpos]
  congr 1
  have hr2 : r ^ 2 = A ^ 2 * σ ^ 2 * (Real.log M / n) := by
    rw [hr, tuning, mul_pow, mul_pow, Real.sq_sqrt (by positivity)]
  have hc2 : c ^ 2 = r ^ 2 * colNorm X j ^ 2 * (n / 2) ^ 2 := by rw [hc]; ring
  rw [hc2, hr2, hcn2]
  field_simp
  ring

lemma aux_t61_event {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {n M : ℕ} (hn : 1 ≤ n) (hM : 2 ≤ M)
    (X : Matrix (Fin n) (Fin M) ℝ) (hcol : ∀ j, colNorm X j ≠ 0)
    (W : Fin n → Ω → ℝ) (σ : ℝ) (hσ : 0 < σ) (hW : GaussianNoise P W σ)
    (A : ℝ) (hA : 0 < A) :
    MeasurableSet (noiseEvent X W (tuning n M A σ)) ∧
      P (noiseEvent X W (tuning n M A σ))ᶜ ≤ ENNReal.ofReal ((M : ℝ) ^ (1 - A ^ 2 / 8)) := by
  obtain ⟨hWm, hWind, hWlaw⟩ := hW
  have hMpos : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hVm : ∀ j, Measurable (noiseCorr X W j) := fun j => by
    unfold noiseCorr
    exact measurable_const.mul (Finset.measurable_sum _ fun i _ => (hWm i).const_mul _)
  refine ⟨?_, ?_⟩
  · have : noiseEvent X W (tuning n M A σ) =
        ⋂ j, {ω | 2 * |noiseCorr X W j ω| ≤ tuning n M A σ * colNorm X j} := by
      ext ω; simp [noiseEvent]
    rw [this]
    exact MeasurableSet.iInter fun j =>
      measurableSet_le (measurable_const.mul (hVm j).abs) measurable_const
  · have hU : (noiseEvent X W (tuning n M A σ))ᶜ =
        ⋃ j, {ω | tuning n M A σ * colNorm X j < 2 * |noiseCorr X W j ω|} := by
      ext ω
      simp [noiseEvent, not_forall, not_le]
    rw [hU]
    refine (measure_iUnion_fintype_le _ _).trans ?_
    refine (Finset.sum_le_sum fun j _ =>
      aux_t61_single hn hM X hcol P W σ hσ hWm hWind hWlaw A hA j).trans (le_of_eq ?_)
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      show (1 : ℝ) - A ^ 2 / 8 = 1 + (-(A ^ 2 / 8)) by ring, Real.rpow_add hMpos, Real.rpow_one,
      ENNReal.ofReal_mul hMpos.le, ENNReal.ofReal_natCast]

/-! ### Deterministic part -/

theorem aux_t61_colNorm_nonneg {n M : ℕ} (X : Matrix (Fin n) (Fin M) ℝ) (j : Fin M) :
    0 ≤ colNorm X j := by
  unfold colNorm empNorm
  exact Real.sqrt_nonneg _

theorem aux_t61_cross {n M : ℕ} (X : Matrix (Fin n) (Fin M) ℝ) (w : Fin n → ℝ)
    (d : Fin M → ℝ) :
    (1 / (n : ℝ)) * ∑ i, w i * X.mulVec d i =
      ∑ j, d j * ((1 / (n : ℝ)) * ∑ i, X i j * w i) := by
  simp only [Matrix.mulVec, dotProduct, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by ring

theorem aux_t61_expand {n : ℕ} (a b : Fin n → ℝ) :
    empSq (fun i => a i - b i) =
      empSq a - 2 * ((1 / (n : ℝ)) * ∑ i, a i * b i) + empSq b := by
  unfold empSq
  have h : ∑ i, (a i - b i) ^ 2 = ∑ i, (a i ^ 2 - 2 * (a i * b i) + b i ^ 2) :=
    Finset.sum_congr rfl fun i _ => by ring
  rw [h, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  ring

theorem aux_t61_basic {n M : ℕ} (X : Matrix (Fin n) (Fin M) ℝ) (f y : Fin n → ℝ) (r : ℝ)
    (hr : 0 < r) (hA : NoiseBound X (fun i => y i - f i) r) (βhat β : Fin M → ℝ)
    (hL : IsLasso X y r βhat) :
    empSq (fun i => X.mulVec βhat i - f i) + r * ∑ j, colNorm X j * |βhat j - β j| ≤
      empSq (fun i => X.mulVec β i - f i) +
        4 * r * ∑ j ∈ supp β, colNorm X j * |βhat j - β j| := by
  have h := hL β
  unfold lassoObj at h
  set w : Fin n → ℝ := fun i => y i - f i with hw
  have hexp : ∀ b : Fin M → ℝ, empSq (fun i => y i - X.mulVec b i) =
      empSq w - 2 * ((1 / (n : ℝ)) * ∑ i, w i * (X.mulVec b i - f i)) +
        empSq (fun i => X.mulVec b i - f i) := by
    intro b
    have := aux_t61_expand w (fun i => X.mulVec b i - f i)
    rw [← this]
    congr 1
    funext i
    simp only [hw]
    ring
  rw [hexp βhat, hexp β] at h
  have hcrossEq : (1 / (n : ℝ)) * ∑ i, w i * (X.mulVec βhat i - f i) -
      (1 / (n : ℝ)) * ∑ i, w i * (X.mulVec β i - f i) =
      ∑ j, (βhat - β) j * ((1 / (n : ℝ)) * ∑ i, X i j * w i) := by
    rw [← aux_t61_cross, ← mul_sub, ← Finset.sum_sub_distrib]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Matrix.mulVec_sub]
    simp only [Pi.sub_apply]
    ring
  have hcrossLe : 2 * ∑ j, (βhat - β) j * ((1 / (n : ℝ)) * ∑ i, X i j * w i) ≤
      r * ∑ j, colNorm X j * |βhat j - β j| := by
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_le_sum fun j _ => ?_
    have hj := hA j
    simp only [Pi.sub_apply]
    set a := (1 / (n : ℝ)) * ∑ i, X i j * w i
    have h1 : (βhat j - β j) * a ≤ |βhat j - β j| * |a| := by
      rw [← abs_mul]; exact le_abs_self _
    have h2 : 0 ≤ |βhat j - β j| := abs_nonneg _
    nlinarith [mul_le_mul_of_nonneg_left hj h2]
  have hpen : ∑ j, colNorm X j * (|βhat j - β j| + |β j| - |βhat j|) ≤
      ∑ j ∈ supp β, 2 * (colNorm X j * |βhat j - β j|) := by
    rw [← Finset.sum_add_sum_compl (supp β)]
    have hc : ∑ j ∈ (supp β)ᶜ, colNorm X j * (|βhat j - β j| + |β j| - |βhat j|) = 0 := by
      refine Finset.sum_eq_zero fun j hj => ?_
      have : β j = 0 := by
        simp only [supp, Finset.mem_compl, Finset.mem_filter, Finset.mem_univ, true_and,
          not_not] at hj
        exact hj
      rw [this]
      simp
    rw [hc, add_zero]
    refine Finset.sum_le_sum fun j _ => ?_
    have h1 : |β j| - |βhat j| ≤ |βhat j - β j| := by
      rw [abs_sub_comm]; exact abs_sub_abs_le_abs_sub _ _
    have h2 := aux_t61_colNorm_nonneg X j
    nlinarith [mul_le_mul_of_nonneg_left h1 h2]
  have hsplit : ∑ j, colNorm X j * (|βhat j - β j| + |β j| - |βhat j|) =
      ∑ j, colNorm X j * |βhat j - β j| + ∑ j, colNorm X j * |β j| -
        ∑ j, colNorm X j * |βhat j| := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [hsplit] at hpen
  rw [← Finset.mul_sum] at hpen
  nlinarith [hcrossEq, hcrossLe, hpen]

theorem aux_t61_fmin_pos {n M : ℕ} (hM : 2 ≤ M) (X : Matrix (Fin n) (Fin M) ℝ)
    (hcol : ∀ j, colNorm X j ≠ 0) : 0 < fmin X := by
  have : Nonempty (Fin M) := ⟨⟨0, by omega⟩⟩
  obtain ⟨j0, hj0⟩ := Finite.exists_min (fun j => colNorm X j)
  have hpos0 : 0 < colNorm X j0 :=
    lt_of_le_of_ne (aux_t61_colNorm_nonneg X j0) (Ne.symm (hcol j0))
  have hfmin_ge : colNorm X j0 ≤ fmin X := le_ciInf hj0
  exact lt_of_lt_of_le hpos0 hfmin_ge

theorem aux_t61_cone {n M : ℕ} (hM : 2 ≤ M) (X : Matrix (Fin n) (Fin M) ℝ)
    (hcol : ∀ j, colNorm X j ≠ 0) (f : Fin n → ℝ) (r : ℝ) (hr : 0 < r) (ε : ℝ) (hε : 0 < ε)
    (βhat β : Fin M → ℝ)
    (hbasic : empSq (fun i => X.mulVec βhat i - f i) + r * ∑ j, colNorm X j * |βhat j - β j| ≤
      empSq (fun i => X.mulVec β i - f i) +
        4 * r * ∑ j ∈ supp β, colNorm X j * |βhat j - β j|)
    (hB24 : ε * empSq (fun i => X.mulVec β i - f i) <
      4 * r * ∑ j ∈ supp β, colNorm X j * |βhat j - β j|) :
    ConeCond ((3 + 4 / ε) * fmax X / fmin X) (supp β) (βhat - β) := by
  set S := ∑ j, colNorm X j * |βhat j - β j| with hS
  set SJ := ∑ j ∈ supp β, colNorm X j * |βhat j - β j| with hSJ
  set SJc := ∑ j ∈ (supp β)ᶜ, colNorm X j * |βhat j - β j| with hSJc
  set Eb := empSq (fun i => X.mulVec β i - f i) with hEb
  have hEhat : 0 ≤ empSq (fun i => X.mulVec βhat i - f i) := by
    unfold empSq
    have : (0 : ℝ) ≤ 1 / (n : ℝ) := by positivity
    exact mul_nonneg this (Finset.sum_nonneg fun i _ => sq_nonneg _)
  have hSJnn : 0 ≤ SJ := Finset.sum_nonneg fun j _ =>
    mul_nonneg (aux_t61_colNorm_nonneg X j) (abs_nonneg _)
  have h1 : S ≤ 4 * (1 + 1 / ε) * SJ := by
    have hrS : r * S ≤ Eb + 4 * r * SJ := by linarith
    have hεrS : ε * (r * S) ≤ ε * (Eb + 4 * r * SJ) := mul_le_mul_of_nonneg_left hrS hε.le
    have key : ε * r * S ≤ ε * r * (4 * (1 + 1 / ε) * SJ) := by
      have e : ε * r * (4 * (1 + 1 / ε) * SJ) = 4 * r * SJ + ε * (4 * r * SJ) := by
        field_simp
        ring
      rw [e]
      nlinarith
    exact le_of_mul_le_mul_left key (mul_pos hε hr)
  have hsum : S = SJ + SJc := by
    rw [hS, hSJ, hSJc, Finset.sum_add_sum_compl]
  have h2 : SJc ≤ (3 + 4 / ε) * SJ := by
    have e : 4 * (1 + 1 / ε) * SJ = (3 + 4 / ε) * SJ + SJ := by ring
    linarith
  have hfmin : 0 < fmin X := aux_t61_fmin_pos hM X hcol
  have hle_fmin : ∀ j, fmin X ≤ colNorm X j := fun j =>
    ciInf_le (Set.finite_range _).bddBelow j
  have hle_fmax : ∀ j, colNorm X j ≤ fmax X := fun j =>
    le_ciSup (Set.finite_range _).bddAbove j
  unfold ConeCond l1On
  simp only [Pi.sub_apply]
  have hA1 : fmin X * ∑ j ∈ (supp β)ᶜ, |βhat j - β j| ≤ SJc := by
    rw [hSJc, Finset.mul_sum]
    exact Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_right (hle_fmin j) (abs_nonneg _)
  have hA2 : SJ ≤ fmax X * ∑ j ∈ supp β, |βhat j - β j| := by
    rw [hSJ, Finset.mul_sum]
    exact Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_right (hle_fmax j) (abs_nonneg _)
  have hc : 0 ≤ 3 + 4 / ε := by positivity
  rw [div_mul_eq_mul_div, le_div_iff₀ hfmin]
  have := mul_le_mul_of_nonneg_left hA2 hc
  nlinarith

/-- `euclNorm v = √n · √(empSq v)`. -/
theorem aux_t61_eucl_emp {n : ℕ} (hn : 1 ≤ n) (v : Fin n → ℝ) :
    euclNorm v = Real.sqrt n * Real.sqrt (empSq v) := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  rw [← Real.sqrt_mul (Nat.cast_nonneg _), euclNorm, empSq]
  congr 1
  field_simp

/-- Triangle inequality for `euclNorm`. -/
theorem aux_t61_eucl_sub {n : ℕ} (u v : Fin n → ℝ) :
    euclNorm (fun i => u i - v i) ≤ euclNorm u + euclNorm v := by
  have hU := Real.sqrt_nonneg (∑ i, u i ^ 2)
  have hV := Real.sqrt_nonneg (∑ i, v i ^ 2)
  have hcs := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ u (fun i => -v i)
  simp only [neg_sq] at hcs
  have hU2 : Real.sqrt (∑ i, u i ^ 2) ^ 2 = ∑ i, u i ^ 2 :=
    Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)
  have hV2 : Real.sqrt (∑ i, v i ^ 2) ^ 2 = ∑ i, v i ^ 2 :=
    Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)
  have hexp : ∑ i, (u i - v i) ^ 2 = ∑ i, u i ^ 2 + 2 * ∑ i, u i * (-v i) + ∑ i, v i ^ 2 := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  unfold euclNorm
  rw [← Real.sqrt_sq (add_nonneg hU hV)]
  apply Real.sqrt_le_sqrt
  rw [hexp]
  nlinarith

/-- The final quadratic inequality. -/
theorem aux_t61_alg (a b K ε : ℝ) (hε : 0 < ε)
    (h : a ^ 2 ≤ b ^ 2 + K * (a + b)) :
    a ^ 2 ≤ (1 + ε) * b ^ 2 + (2 + ε) ^ 2 * K ^ 2 / (4 * ε) := by
  have hc : 0 ≤ 2 * ε * (2 + ε) := by positivity
  have h' := mul_le_mul_of_nonneg_left h hc
  have key : 4 * ε * a ^ 2 ≤ 4 * ε * ((1 + ε) * b ^ 2) + (2 + ε) ^ 2 * K ^ 2 := by
    nlinarith [sq_nonneg (2 * ε * a - (2 + ε) * K), sq_nonneg (2 * ε * b - (2 + ε) * K)]
  have h4 : 0 < 4 * ε := by positivity
  rw [← sub_nonneg]
  have e : (1 + ε) * b ^ 2 + (2 + ε) ^ 2 * K ^ 2 / (4 * ε) - a ^ 2 =
      (4 * ε * ((1 + ε) * b ^ 2) + (2 + ε) ^ 2 * K ^ 2 - 4 * ε * a ^ 2) / (4 * ε) := by
    field_simp
  rw [e]
  exact div_nonneg (by linarith) h4.le

theorem aux_t61_det {n M : ℕ} (hn : 1 ≤ n) (hM : 2 ≤ M) (X : Matrix (Fin n) (Fin M) ℝ)
    (hcol : ∀ j, colNorm X j ≠ 0) (f y : Fin n → ℝ) (r : ℝ) (hr : 0 < r)
    (hA : NoiseBound X (fun i => y i - f i) r) (ε : ℝ) (hε : 0 < ε) (γ : ℝ) (hγ : 0 < γ)
    (s : ℕ) (βhat : Fin M → ℝ) (hL : IsLasso X y r βhat) (β : Fin M → ℝ)
    (hβ : β ∈ LambdaSet X s γ ((3 + 4 / ε) * fmax X / fmin X)) :
    empSq (fun i => X.mulVec βhat i - f i) ≤
      (1 + ε) * (empSq (fun i => X.mulVec β i - f i) +
        4 * (2 + ε) ^ 2 / (ε * (1 + ε)) * fmax X ^ 2 * r ^ 2 / γ ^ 2 * (sparsity β : ℝ)) := by
  have hbasic := aux_t61_basic X f y r hr hA βhat β hL
  set a2 := empSq (fun i => X.mulVec βhat i - f i) with ha2
  set b2 := empSq (fun i => X.mulVec β i - f i) with hb2
  set T := ∑ j ∈ supp β, colNorm X j * |βhat j - β j| with hT
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hemp_nn : ∀ v : Fin n → ℝ, 0 ≤ empSq v := fun v => by
    unfold empSq
    exact mul_nonneg (by positivity) (Finset.sum_nonneg fun i _ => sq_nonneg _)
  have ha2nn : 0 ≤ a2 := hemp_nn _
  have hb2nn : 0 ≤ b2 := hemp_nn _
  have hSall : 0 ≤ ∑ j, colNorm X j * |βhat j - β j| :=
    Finset.sum_nonneg fun j _ => mul_nonneg (aux_t61_colNorm_nonneg X j) (abs_nonneg _)
  have hTnn : 0 ≤ T := Finset.sum_nonneg fun j _ =>
    mul_nonneg (aux_t61_colNorm_nonneg X j) (abs_nonneg _)
  have hfmin : 0 < fmin X := aux_t61_fmin_pos hM X hcol
  have hle_fmax : ∀ j, colNorm X j ≤ fmax X := fun j =>
    le_ciSup (Set.finite_range _).bddAbove j
  have hfmax_nn : 0 ≤ fmax X := le_trans (aux_t61_colNorm_nonneg X ⟨0, by omega⟩)
    (hle_fmax _)
  have hextra : 0 ≤ 4 * (2 + ε) ^ 2 / (ε * (1 + ε)) * fmax X ^ 2 * r ^ 2 / γ ^ 2 *
      (sparsity β : ℝ) := by positivity
  have hmain : a2 ≤ b2 + 4 * r * T := by nlinarith
  by_cases hB24 : ε * b2 < 4 * r * T
  · -- cone case
    have hcone := aux_t61_cone hM X hcol f r hr ε hε βhat β hbasic hB24
    have hδ : βhat - β ≠ 0 := by
      intro h0
      have hT0 : T = 0 := by
        rw [hT]
        refine Finset.sum_eq_zero fun j _ => ?_
        have : βhat j - β j = 0 := by
          have := congrFun h0 j
          simpa using this
        rw [this]; simp
      rw [hT0] at hB24
      nlinarith
    have hRE := hβ.2 (βhat - β) hδ hcone
    -- bound T by fmax * √𝓜 * l2On
    set δ := βhat - β with hδdef
    have hT1 : T ≤ fmax X * ∑ j ∈ supp β, |δ j| := by
      rw [hT, Finset.mul_sum]
      exact Finset.sum_le_sum fun j _ => by
        simp only [hδdef, Pi.sub_apply]
        exact mul_le_mul_of_nonneg_right (hle_fmax j) (abs_nonneg _)
    have hT2 : ∑ j ∈ supp β, |δ j| ≤ Real.sqrt (sparsity β) * l2On δ (supp β) := by
      have hcs := Real.sum_mul_le_sqrt_mul_sqrt (supp β) (fun j => |δ j|) (fun _ => (1 : ℝ))
      simp only [mul_one, one_pow, Finset.sum_const, nsmul_eq_mul, sq_abs] at hcs
      rw [l2On, sparsity, mul_comm]
      exact hcs
    -- euclNorm (X δ) ≤ √n (a + b)
    set a := Real.sqrt a2 with ha
    set b := Real.sqrt b2 with hb
    have hann : 0 ≤ a := Real.sqrt_nonneg _
    have hbnn : 0 ≤ b := Real.sqrt_nonneg _
    have hXδ : euclNorm (X.mulVec δ) ≤ Real.sqrt n * (a + b) := by
      have heq : X.mulVec δ = fun i => (X.mulVec βhat i - f i) - (X.mulVec β i - f i) := by
        funext i
        rw [hδdef, Matrix.mulVec_sub]
        simp only [Pi.sub_apply]
        ring
      rw [heq]
      refine (aux_t61_eucl_sub _ _).trans (le_of_eq ?_)
      rw [aux_t61_eucl_emp hn, aux_t61_eucl_emp hn, ha, hb, ha2, hb2]
      ring
    have hsqn : 0 < Real.sqrt n := Real.sqrt_pos.2 hnpos
    have hl2 : γ * l2On δ (supp β) ≤ a + b := by
      have : Real.sqrt n * (γ * l2On δ (supp β)) ≤ Real.sqrt n * (a + b) := by
        calc Real.sqrt n * (γ * l2On δ (supp β)) = γ * Real.sqrt n * l2On δ (supp β) := by ring
          _ ≤ euclNorm (X.mulVec δ) := hRE
          _ ≤ Real.sqrt n * (a + b) := hXδ
      exact le_of_mul_le_mul_left this hsqn
    set K := 4 * r * fmax X * Real.sqrt (sparsity β) / γ with hK
    have hsq_nn : 0 ≤ Real.sqrt (sparsity β) := Real.sqrt_nonneg _
    have hl2nn : 0 ≤ l2On δ (supp β) := Real.sqrt_nonneg _
    have h4rT : 4 * r * T ≤ K * (a + b) := by
      have step1 : 4 * r * T ≤ 4 * r * fmax X * Real.sqrt (sparsity β) * l2On δ (supp β) := by
        have := mul_le_mul_of_nonneg_left hT2 hfmax_nn
        have h2 : T ≤ fmax X * (Real.sqrt (sparsity β) * l2On δ (supp β)) := hT1.trans this
        have h4r : 0 ≤ 4 * r := by positivity
        have := mul_le_mul_of_nonneg_left h2 h4r
        linarith [this]
      have step2 : 4 * r * fmax X * Real.sqrt (sparsity β) * l2On δ (supp β) ≤ K * (a + b) := by
        rw [hK, div_mul_eq_mul_div, le_div_iff₀ hγ]
        have hc : 0 ≤ 4 * r * fmax X * Real.sqrt (sparsity β) := by positivity
        have := mul_le_mul_of_nonneg_left hl2 hc
        linarith
      linarith
    have ha2eq : a ^ 2 = a2 := Real.sq_sqrt ha2nn
    have hb2eq : b ^ 2 = b2 := Real.sq_sqrt hb2nn
    have halg := aux_t61_alg a b K ε hε (by rw [ha2eq, hb2eq]; linarith)
    rw [ha2eq, hb2eq] at halg
    have hsp : Real.sqrt (sparsity β) ^ 2 = (sparsity β : ℝ) := Real.sq_sqrt (Nat.cast_nonneg _)
    have hKsq : (2 + ε) ^ 2 * K ^ 2 / (4 * ε) = (1 + ε) *
        (4 * (2 + ε) ^ 2 / (ε * (1 + ε)) * fmax X ^ 2 * r ^ 2 / γ ^ 2 * (sparsity β : ℝ)) := by
      rw [hK, div_pow, mul_pow, hsp]
      field_simp
    rw [hKsq] at halg
    linarith
  · push Not at hB24
    nlinarith

end LassoDantzig.Oracle

open LassoDantzig.Oracle
open MeasureTheory ProbabilityTheory

theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {n M : ℕ} (hn : 1 ≤ n) (hM : 2 ≤ M)
    (X : Matrix (Fin n) (Fin M) ℝ) (hcol : ∀ j, colNorm X j ≠ 0) (f : Fin n → ℝ)
    (W : Fin n → Ω → ℝ) (σ : ℝ) (hσ : 0 < σ) (hW : GaussianNoise P W σ)
    (ε : ℝ) (hε : 0 < ε) (s : ℕ) (hs1 : 1 ≤ s) (hsM : s ≤ M)
    (κ : ℝ) (hκ : 0 < κ) (hRE : RE X s ((3 + 4 / ε) * fmax X / fmin X) κ)
    (A : ℝ) (hA : 2 * Real.sqrt 2 < A) :
    ∃ E : Set Ω, MeasurableSet E ∧ 1 - (M : ℝ) ^ (1 - A ^ 2 / 8) ≤ (P E).toReal ∧
      ∀ ω ∈ E, ∀ βhat : Fin M → ℝ, IsLasso X (fun i => f i + W i ω) (tuning n M A σ) βhat →
        ∀ β : Fin M → ℝ, sparsity β ≤ s →
          empSq (fun i => X.mulVec βhat i - f i) ≤
            (1 + ε) * (empSq (fun i => X.mulVec β i - f i) +
              4 * (2 + ε) ^ 2 / (ε * (1 + ε)) * fmax X ^ 2 * A ^ 2 * σ ^ 2 / κ ^ 2 *
                ((sparsity β : ℝ) * Real.log M / n)) := by
  have hApos : 0 < A := lt_of_le_of_lt (by positivity) hA
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hM' : (2 : ℝ) ≤ M := by exact_mod_cast hM
  have hlogM : 0 < Real.log M := Real.log_pos (by linarith)
  obtain ⟨hmeas, hprob⟩ := aux_t61_event P hn hM X hcol W σ hσ hW A hApos
  refine ⟨noiseEvent X W (tuning n M A σ), hmeas, ?_, ?_⟩
  · have hrpow : 0 ≤ (M : ℝ) ^ (1 - A ^ 2 / 8) := Real.rpow_nonneg (by linarith) _
    have hc : (P (noiseEvent X W (tuning n M A σ))ᶜ).toReal ≤ (M : ℝ) ^ (1 - A ^ 2 / 8) :=
      ENNReal.toReal_le_of_le_ofReal hrpow hprob
    rw [prob_compl_eq_one_sub hmeas, ENNReal.toReal_sub_of_le prob_le_one ENNReal.one_ne_top,
      ENNReal.toReal_one] at hc
    linarith
  · intro ω hω βhat hL β hβs
    have hβ : β ∈ LambdaSet X s κ ((3 + 4 / ε) * fmax X / fmin X) := by
      refine ⟨hβs, ?_⟩
      intro δ hδ hcone
      exact hRE (supp β) hβs δ hδ hcone
    have hr : 0 < tuning n M A σ := by
      unfold tuning; positivity
    have hNB : NoiseBound X (fun i => (f i + W i ω) - f i) (tuning n M A σ) := by
      intro j
      have := hω j
      simp only [noiseCorr] at this
      simpa using this
    have hdet := aux_t61_det hn hM X hcol f (fun i => f i + W i ω) (tuning n M A σ) hr hNB ε hε
      κ hκ s βhat hL β hβ
    have hr2 : tuning n M A σ ^ 2 = A ^ 2 * σ ^ 2 * (Real.log M / n) := by
      rw [tuning, mul_pow, mul_pow, Real.sq_sqrt (by positivity)]
    rw [hr2] at hdet
    convert hdet using 3
    ring
