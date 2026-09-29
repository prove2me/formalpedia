-- Prove2me | solution 1 for LassoDantzig.Oracle.lemma_B1
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T04:07:27.360963+00:00
-- url     : https://prove2.me/submissions/88c45e6b-a636-4c17-a53b-517de0b90bc2

import Mathlib
import Definitions.Def_LassoDantzig_Oracle_Model

open MeasureTheory ProbabilityTheory

namespace LassoDantzig.Oracle


open Real Set Filter Topology in
lemma aux_B1_tail (v : NNReal) (hv : 0 < (v : ℝ)) (s : ℝ) (hs : 0 < s)
    (hvs : 2 * (v : ℝ) ≤ π * s ^ 2) :
    gaussianReal 0 v {x | s < |x|} ≤ ENNReal.ofReal (Real.exp (-s ^ 2 / (2 * v))) := by
  have hv0 : v ≠ 0 := by
    intro h; rw [h] at hv; simp at hv
  set φ := gaussianPDFReal 0 v with hφ
  have hderiv : ∀ x, HasDerivAt (fun x => -(v:ℝ) * φ x) (x * φ x) x := by
    intro x
    have h1 : HasDerivAt (fun x : ℝ => -(x - 0) ^ 2 / (2 * (v:ℝ))) (-(2 * x) / (2 * v)) x := by
      have := (((hasDerivAt_id x).sub_const 0).pow 2).neg.div_const (2 * (v:ℝ))
      refine this.congr_deriv ?_
      simp
    have h2 := (h1.exp).const_mul (-(v:ℝ) * (√(2 * π * v))⁻¹)
    have hf : (fun x => -(v:ℝ) * φ x) =
        fun y => -(v:ℝ) * (√(2 * π * v))⁻¹ * rexp (-(y - 0) ^ 2 / (2 * v)) := by
      funext y; simp only [hφ, gaussianPDFReal]; ring
    rw [hf]
    refine h2.congr_deriv ?_
    simp only [hφ, gaussianPDFReal]
    field_simp
  have hlim : Tendsto (fun x => -(v:ℝ) * φ x) atTop (𝓝 0) := by
    have h0 : Tendsto (fun x : ℝ => -(x - 0) ^ 2 / (2 * (v:ℝ))) atTop atBot := by
      simp only [sub_zero]
      exact (tendsto_neg_atTop_atBot.comp (tendsto_pow_atTop two_ne_zero)).atBot_div_const
        (by positivity)
    have h1 := (Real.tendsto_exp_atBot.comp h0).const_mul (-(v:ℝ) * (√(2 * π * v))⁻¹)
    simp only [mul_zero] at h1
    convert h1 using 1
    funext y; simp only [hφ, gaussianPDFReal, Function.comp]; ring
  have hnn : ∀ x ∈ Ioi s, 0 ≤ x * φ x := fun x hx =>
    mul_nonneg (le_trans hs.le (le_of_lt hx)) (gaussianPDFReal_nonneg _ _ _)
  have hint : IntegrableOn (fun x => x * φ x) (Ioi s) :=
    integrableOn_Ioi_deriv_of_nonneg' (fun x _ => hderiv x) hnn hlim
  have hval : ∫ x in Ioi s, x * φ x = v * φ s := by
    rw [integral_Ioi_of_hasDerivAt_of_nonneg' (fun x _ => hderiv x) hnn hlim]; ring
  have hIoi : gaussianReal 0 v (Ioi s) ≤ ENNReal.ofReal (v * φ s / s) := by
    rw [gaussianReal_apply_eq_integral _ hv0]
    apply ENNReal.ofReal_le_ofReal
    calc ∫ x in Ioi s, gaussianPDFReal 0 v x ≤ ∫ x in Ioi s, (1 / s) * (x * φ x) := by
          apply setIntegral_mono_on (integrable_gaussianPDFReal _ _).integrableOn
            (hint.const_mul _) measurableSet_Ioi
          intro x hx
          rw [show (1 / s) * (x * φ x) = (x / s) * φ x by ring]
          exact le_mul_of_one_le_left (gaussianPDFReal_nonneg _ _ _)
            (by rw [le_div_iff₀ hs]; linarith [mem_Ioi.mp hx])
      _ = v * φ s / s := by rw [integral_const_mul, hval]; ring
  have hIio : gaussianReal 0 v (Iio (-s)) = gaussianReal 0 v (Ioi s) := by
    have hm : (gaussianReal 0 v).map (fun x => -x) = gaussianReal 0 v := by
      rw [gaussianReal_map_neg, neg_zero]
    rw [← hm, Measure.map_apply measurable_neg measurableSet_Iio, hm]
    congr 1
    ext x; simp
  have hsub : {x : ℝ | s < |x|} ⊆ Iio (-s) ∪ Ioi s := by
    intro x hx
    rcases lt_abs.mp (show s < |x| from hx) with h | h
    · exact Or.inr h
    · exact Or.inl (by simp; linarith)
  have hfin : 2 * (v:ℝ) * φ s / s ≤ Real.exp (-s ^ 2 / (2 * v)) := by
    have hsq : 2 * v / s ≤ √(2 * π * v) := by
      rw [Real.le_sqrt (by positivity) (by positivity), div_pow, div_le_iff₀ (by positivity)]
      nlinarith
    have hpos : 0 < √(2 * π * v) := by positivity
    have hE : 0 ≤ Real.exp (-s ^ 2 / (2 * v)) := (Real.exp_pos _).le
    simp only [hφ, gaussianPDFReal, sub_zero]
    calc 2 * (v:ℝ) * ((√(2 * π * v))⁻¹ * rexp (-s ^ 2 / (2 * v))) / s
        = (2 * v / s) * (√(2 * π * v))⁻¹ * rexp (-s ^ 2 / (2 * v)) := by ring
      _ ≤ √(2 * π * v) * (√(2 * π * v))⁻¹ * rexp (-s ^ 2 / (2 * v)) := by
          gcongr
      _ = rexp (-s ^ 2 / (2 * v)) := by field_simp
  calc gaussianReal 0 v {x | s < |x|} ≤ gaussianReal 0 v (Iio (-s) ∪ Ioi s) := measure_mono hsub
    _ ≤ gaussianReal 0 v (Iio (-s)) + gaussianReal 0 v (Ioi s) := measure_union_le _ _
    _ ≤ ENNReal.ofReal (v * φ s / s) + ENNReal.ofReal (v * φ s / s) := by
        rw [hIio]; exact add_le_add hIoi hIoi
    _ = ENNReal.ofReal (2 * v * φ s / s) := by
        have : 0 ≤ (v:ℝ) * φ s / s := by
          have := gaussianPDFReal_nonneg 0 v s; positivity
        rw [← ENNReal.ofReal_add this this]; congr 1; ring
    _ ≤ _ := ENNReal.ofReal_le_ofReal hfin



lemma aux_B1_law {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {n : ℕ} (W : Fin n → Ω → ℝ) (σ : ℝ) (hW : GaussianNoise P W σ) (a : Fin n → ℝ) :
    P.map (fun ω => ∑ i, a i * W i ω) = gaussianReal 0 (σ ^ 2 * ∑ i, a i ^ 2).toNNReal := by
  obtain ⟨hmeas, hind, hlaw⟩ := hW
  have hWG : ∀ i, HasGaussianLaw (W i) P := fun i =>
    (⟨(hmeas i).aemeasurable, hlaw i⟩ :
      HasLaw (W i) (gaussianReal 0 (σ ^ 2).toNNReal) P).hasGaussianLaw
  have hG : ∀ i, HasGaussianLaw (fun ω => a i * W i ω) P := fun i => by
    simpa using (hWG i).fun_smul (a i)
  have hind' : iIndepFun (fun i ω => a i * W i ω) P :=
    hind.comp (fun i x => a i * x) (fun i => measurable_const.mul measurable_id)
  have hS := iIndepFun.hasGaussianLaw_fun_sum hG hind'
  rw [hS.map_eq_gaussianReal]
  congr 1
  · rw [integral_finsetSum _ (fun i _ => (hG i).integrable)]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [integral_const_mul]
    have : ∫ ω, W i ω ∂P = 0 := by
      have h := integral_map (μ := P) (φ := W i) (f := fun x : ℝ => x) (hmeas i).aemeasurable
        aestronglyMeasurable_id
      rw [hlaw i] at h
      rw [← h]
      simp
    rw [this, mul_zero]
  · congr 1
    have : (fun ω => ∑ i, a i * W i ω) = ∑ i, (fun ω => a i * W i ω) := by
      funext ω; simp
    rw [this, IndepFun.variance_sum (fun i _ => (hG i).memLp_two)
      (fun i _ j _ hij => hind'.indepFun hij)]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [variance_const_mul]
    have : variance (W i) P = σ ^ 2 := by
      rw [← variance_id_map (hmeas i).aemeasurable, hlaw i, variance_id_gaussianReal]
      simp [sq_nonneg]
    rw [this]; ring



lemma aux_B1_det {n M : ℕ} (X : Matrix (Fin n) (Fin M) ℝ) (f w : Fin n → ℝ) (r : ℝ)
    (hr : 0 ≤ r)
    (hw : ∀ j, 2 * |(1 / (n : ℝ)) * ∑ i, X i j * w i| ≤ r * colNorm X j)
    (βhat : Fin M → ℝ) (hL : IsLasso X (fun i => f i + w i) r βhat) (β : Fin M → ℝ) :
    empSq (fun i => X.mulVec βhat i - f i) + r * ∑ j, colNorm X j * |βhat j - β j| ≤
      empSq (fun i => X.mulVec β i - f i) +
        4 * r * ∑ j ∈ supp β, colNorm X j * |βhat j - β j| := by
  have hcn : ∀ j, 0 ≤ colNorm X j := fun j => Real.sqrt_nonneg _
  have key := hL β
  unfold lassoObj at key
  beta_reduce at key
  set V : Fin M → ℝ := fun j => (1 / (n : ℝ)) * ∑ i, X i j * w i with hV
  have hcross : ∀ γ : Fin M → ℝ, (1 / (n : ℝ)) * ∑ i, w i * X.mulVec γ i = ∑ j, γ j * V j := by
    intro γ
    simp only [hV, Matrix.mulVec, dotProduct, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun i _ => by ring))
  have hexp : ∀ γ : Fin M → ℝ, empSq (fun i => f i + w i - X.mulVec γ i) =
      empSq (fun i => X.mulVec γ i - f i) - 2 * ((1 / (n : ℝ)) * ∑ i, w i * X.mulVec γ i) +
        2 * ((1 / (n : ℝ)) * ∑ i, w i * f i) + empSq w := by
    intro γ
    unfold empSq
    have : ∀ i, (f i + w i - X.mulVec γ i) ^ 2 = (X.mulVec γ i - f i) ^ 2 -
        2 * (w i * X.mulVec γ i) + 2 * (w i * f i) + w i ^ 2 := fun i => by ring
    simp_rw [this, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
    ring
  rw [hexp, hexp, hcross, hcross] at key
  have F1 : 2 * (∑ j, βhat j * V j - ∑ j, β j * V j) ≤
      r * ∑ j, colNorm X j * |βhat j - β j| := by
    rw [← Finset.sum_sub_distrib, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_le_sum fun j _ => ?_
    have h1 : 2 * |V j| ≤ r * colNorm X j := hw j
    have h2 : βhat j * V j - β j * V j ≤ |βhat j - β j| * |V j| := by
      rw [← sub_mul, ← abs_mul]; exact le_abs_self _
    nlinarith [mul_le_mul_of_nonneg_left h1 (abs_nonneg (βhat j - β j))]
  have F2 : ∑ j, colNorm X j * |βhat j - β j| + ∑ j, colNorm X j * |β j| -
      ∑ j, colNorm X j * |βhat j| ≤ 2 * ∑ j ∈ supp β, colNorm X j * |βhat j - β j| := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib, supp, Finset.sum_filter,
      Finset.mul_sum]
    refine Finset.sum_le_sum fun j _ => ?_
    split_ifs with h
    · have h2 : |β j| - |βhat j| ≤ |βhat j - β j| := by
        rw [abs_sub_comm]; exact abs_sub_abs_le_abs_sub _ _
      nlinarith [mul_le_mul_of_nonneg_left h2 (hcn j)]
    · rw [not_not.mp h]; simp
  have F2' := mul_le_mul_of_nonneg_left F2 hr
  nlinarith

lemma aux_B1_cs {n M : ℕ} (X : Matrix (Fin n) (Fin M) ℝ) (a : ℝ) (r : ℝ) (hr : 0 ≤ r)
    (βhat β : Fin M → ℝ) :
    a + 4 * r * ∑ j ∈ supp β, colNorm X j * |βhat j - β j| ≤
      a + 4 * r * Real.sqrt (sparsity β) *
        Real.sqrt (∑ j ∈ supp β, colNorm X j ^ 2 * |βhat j - β j| ^ 2) := by
  have hCS : ∑ j ∈ supp β, colNorm X j * |βhat j - β j| ≤ Real.sqrt (sparsity β) *
      Real.sqrt (∑ j ∈ supp β, colNorm X j ^ 2 * |βhat j - β j| ^ 2) := by
    rw [← Real.sqrt_mul (Nat.cast_nonneg _)]
    refine le_trans (le_abs_self _) (Real.abs_le_sqrt ?_)
    have := sq_sum_le_card_mul_sum_sq (s := supp β) (f := fun j => colNorm X j * |βhat j - β j|)
    simp only [mul_pow] at this
    simpa [sparsity] using this
  have := mul_le_mul_of_nonneg_left hCS (by positivity : 0 ≤ 4 * r)
  nlinarith


lemma aux_B1_meas {Ω : Type*} [MeasurableSpace Ω] {n M : ℕ} (X : Matrix (Fin n) (Fin M) ℝ)
    (W : Fin n → Ω → ℝ) (hm : ∀ i, Measurable (W i)) (j : Fin M) :
    Measurable (fun ω => noiseCorr X W j ω) := by
  unfold noiseCorr
  exact (Finset.measurable_sum _ fun i _ => (hm i).const_mul _).const_mul _

end LassoDantzig.Oracle

open LassoDantzig.Oracle
open MeasureTheory ProbabilityTheory

theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {n M : ℕ} (hn : 1 ≤ n) (hM : 2 ≤ M)
    (X : Matrix (Fin n) (Fin M) ℝ) (hcol : ∀ j, colNorm X j ≠ 0) (f : Fin n → ℝ)
    (W : Fin n → Ω → ℝ) (σ : ℝ) (hσ : 0 < σ) (hW : GaussianNoise P W σ)
    (A : ℝ) (hA : 2 * Real.sqrt 2 < A) :
    ∃ E : Set Ω, MeasurableSet E ∧ 1 - (M : ℝ) ^ (1 - A ^ 2 / 8) ≤ (P E).toReal ∧
      ∀ ω ∈ E, ∀ βhat : Fin M → ℝ, IsLasso X (fun i => f i + W i ω) (tuning n M A σ) βhat →
        ∀ β : Fin M → ℝ,
          empSq (fun i => X.mulVec βhat i - f i) +
                tuning n M A σ * ∑ j, colNorm X j * |βhat j - β j| ≤
              empSq (fun i => X.mulVec β i - f i) +
                4 * tuning n M A σ * ∑ j ∈ supp β, colNorm X j * |βhat j - β j| ∧
            empSq (fun i => X.mulVec β i - f i) +
                4 * tuning n M A σ * ∑ j ∈ supp β, colNorm X j * |βhat j - β j| ≤
              empSq (fun i => X.mulVec β i - f i) +
                4 * tuning n M A σ * Real.sqrt (sparsity β) *
                  Real.sqrt (∑ j ∈ supp β, colNorm X j ^ 2 * |βhat j - β j| ^ 2) := by
  set r := tuning n M A σ with hr
  have hA0 : 0 < A := lt_trans (by positivity) hA
  have hA2 : 8 < A ^ 2 := by
    have h8 : (2 * Real.sqrt 2) ^ 2 = 8 := by
      rw [mul_pow, Real.sq_sqrt (by norm_num)]; norm_num
    nlinarith [Real.sqrt_nonneg 2]
  have hn0 : (0:ℝ) < n := Nat.cast_pos.mpr (by omega)
  have hM1 : (1:ℝ) < M := by exact_mod_cast (by omega : 1 < M)
  have hM0 : (0:ℝ) < M := by linarith
  have hlogM : 0 < Real.log M := Real.log_pos hM1
  have hlog2 : Real.log 2 ≤ Real.log M :=
    Real.log_le_log (by norm_num) (by exact_mod_cast hM)
  have hr0 : 0 < r := by
    simp only [hr, tuning]
    have : 0 < Real.log M / n := div_pos hlogM hn0
    positivity
  have hr2 : r ^ 2 = A ^ 2 * σ ^ 2 * (Real.log M / n) := by
    rw [hr, tuning, mul_pow, mul_pow, Real.sq_sqrt (div_nonneg hlogM.le hn0.le)]
  have hEdef : noiseEvent X W r = ⋂ j, {ω | 2 * |noiseCorr X W j ω| ≤ r * colNorm X j} := by
    ext ω; simp [noiseEvent]
  have hEm : MeasurableSet (noiseEvent X W r) := by
    rw [hEdef]
    exact MeasurableSet.iInter fun j =>
      measurableSet_le ((continuous_abs.measurable.comp (aux_B1_meas X W hW.1 j)).const_mul 2)
        measurable_const
  refine ⟨noiseEvent X W r, hEm, ?_, ?_⟩
  swap
  · intro ω hω βhat hL β
    exact ⟨aux_B1_det X f (fun i => W i ω) r hr0.le hω βhat hL β,
      aux_B1_cs X _ r hr0.le βhat β⟩
  -- probability bound
  set L := Real.log M with hL
  have hbound : ∀ j, P {ω | r * colNorm X j / 2 < |noiseCorr X W j ω|} ≤
      ENNReal.ofReal (Real.exp (-(A ^ 2 * L / 8))) := by
    intro j
    set c := colNorm X j with hc
    have hc0 : 0 < c := lt_of_le_of_ne (Real.sqrt_nonneg _) (Ne.symm (hcol j))
    have hc2 : c ^ 2 = (1 / (n:ℝ)) * ∑ i, X i j ^ 2 := by
      rw [hc, colNorm, empNorm, Real.sq_sqrt]
      · rfl
      · unfold empSq; positivity
    have hfun : (fun ω => noiseCorr X W j ω) = fun ω => ∑ i, ((1 / (n:ℝ)) * X i j) * W i ω := by
      funext ω; rw [noiseCorr, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring
    have hlaw := aux_B1_law P W σ hW (fun i => (1 / (n:ℝ)) * X i j)
    rw [← hfun] at hlaw
    set v : NNReal := (σ ^ 2 * ∑ i, ((1 / (n:ℝ)) * X i j) ^ 2).toNNReal with hv
    have hvr : (v : ℝ) = σ ^ 2 * c ^ 2 / n := by
      rw [hv, Real.coe_toNNReal _ (by positivity), hc2]
      simp_rw [mul_pow, ← Finset.mul_sum]
      field_simp
    have hvpos : 0 < (v : ℝ) := by rw [hvr]; positivity
    have hmeasV := aux_B1_meas X W hW.1 j
    have hset : {ω | r * c / 2 < |noiseCorr X W j ω|} =
        (fun ω => noiseCorr X W j ω) ⁻¹' {x | r * c / 2 < |x|} := rfl
    rw [hset, ← Measure.map_apply hmeasV
      (measurableSet_lt measurable_const continuous_abs.measurable), hlaw]
    have hs : 0 < r * c / 2 := by positivity
    have hpi : 2 * (v : ℝ) ≤ Real.pi * (r * c / 2) ^ 2 := by
      have hpiA : 8 ≤ Real.pi * A ^ 2 * L := by
        have hpi3 := Real.pi_gt_three
        have hl2 := Real.log_two_gt_d9
        have hL' : (0.69:ℝ) ≤ L := by linarith
        have h1 : 24 ≤ Real.pi * A ^ 2 := by nlinarith
        calc (8:ℝ) ≤ 24 * 0.69 := by norm_num
          _ ≤ Real.pi * A ^ 2 * L := mul_le_mul h1 hL' (by norm_num) (by positivity)
      rw [hvr, show (r * c / 2) ^ 2 = r ^ 2 * c ^ 2 / 4 by ring, hr2]
      have : Real.pi * (A ^ 2 * σ ^ 2 * (L / n) * c ^ 2 / 4) =
          (Real.pi * A ^ 2 * L) * (σ ^ 2 * c ^ 2 / n) / 4 := by ring
      rw [this]
      have hpos : 0 ≤ σ ^ 2 * c ^ 2 / n := by positivity
      nlinarith
    have key := aux_B1_tail v hvpos (r * c / 2) hs hpi
    have hexp : -(r * c / 2) ^ 2 / (2 * (v:ℝ)) = -(A ^ 2 * L / 8) := by
      rw [hvr]
      have : (r * c / 2) ^ 2 = r ^ 2 * c ^ 2 / 4 := by ring
      rw [this, hr2]
      field_simp
      norm_num
    rw [hexp] at key
    exact key
  have hcompl : (noiseEvent X W r)ᶜ ⊆ ⋃ j, {ω | r * colNorm X j / 2 < |noiseCorr X W j ω|} := by
    intro ω hω
    simp only [noiseEvent, Set.mem_compl_iff, Set.mem_ofPred_eq, not_forall, not_le] at hω
    obtain ⟨j, hj⟩ := hω
    exact Set.mem_iUnion.mpr ⟨j, by show r * colNorm X j / 2 < _; linarith⟩
  have hPc : P (noiseEvent X W r)ᶜ ≤ ENNReal.ofReal ((M : ℝ) ^ (1 - A ^ 2 / 8)) := by
    calc P (noiseEvent X W r)ᶜ ≤ P (⋃ j, {ω | r * colNorm X j / 2 < |noiseCorr X W j ω|}) :=
          measure_mono hcompl
      _ ≤ ∑ j, P {ω | r * colNorm X j / 2 < |noiseCorr X W j ω|} := measure_iUnion_fintype_le _ _
      _ ≤ ∑ _j : Fin M, ENNReal.ofReal (Real.exp (-(A ^ 2 * L / 8))) :=
          Finset.sum_le_sum fun j _ => hbound j
      _ = ENNReal.ofReal ((M : ℝ) ^ (1 - A ^ 2 / 8)) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
            ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _),
            Real.rpow_def_of_pos hM0, ← hL]
          congr 1
          rw [show L * (1 - A ^ 2 / 8) = L + -(A ^ 2 * L / 8) by ring, Real.exp_add, hL,
            Real.exp_log hM0]
  have hsum : (P (noiseEvent X W r)).toReal + (P (noiseEvent X W r)ᶜ).toReal = 1 := by
    rw [← ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _),
      measure_add_measure_compl hEm, measure_univ, ENNReal.toReal_one]
  have := ENNReal.toReal_le_of_le_ofReal (by positivity) hPc
  linarith
