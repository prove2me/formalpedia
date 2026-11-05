-- Prove2me | solution 1 for ModernOnlineLearning.Portfolio.theorem_10_1_uniform
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T13:58:03.420826+00:00
-- url     : https://prove2.me/submissions/ca6cfaf9-e04e-4c94-8296-ec925ebf7ff7

import Mathlib
import Definitions.Def_ModernOnlineLearning_Portfolio_Setting
import Theorems.Thm_ModernOnlineLearning_Portfolio_eq_10_5
import Theorems.Thm_ModernOnlineLearning_Portfolio_lemma_10_6
import Theorems.Thm_ModernOnlineLearning_Portfolio_theorem_10_4
import Theorems.Thm_ModernOnlineLearning_Portfolio_lemma_10_3
set_option autoImplicit false

open ModernOnlineLearning.Portfolio MeasureTheory

/-- binomial bound -/
theorem binom_bound_aux {d T : ℕ} (hd : 2 ≤ d) :
    Real.log (((T + d - 1).choose (d - 1) : ℕ) : ℝ) ≤
      ((d - 1 : ℕ) : ℝ) *
        (Real.log ((T : ℝ) / ((d - 1 : ℕ) : ℝ) + 1) + 1) := by
  obtain ⟨k, rfl⟩ : ∃ k, d = k + 1 := ⟨d - 1, by omega⟩
  have hk : 1 ≤ k := by omega
  simp only [Nat.add_sub_cancel]
  have hTk : T + (k + 1) - 1 = T + k := by omega
  rw [hTk]
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
  have hn : (0 : ℝ) < (T + k : ℕ) := by push_cast; positivity
  have hCpos : (0 : ℝ) < ((T + k).choose k : ℕ) := by
    exact_mod_cast Nat.choose_pos (by omega)
  have h1 : (((T + k).choose k : ℕ) : ℝ) ≤ ((T + k : ℕ) : ℝ) ^ k / k.factorial :=
    Nat.choose_le_pow_div k (T + k)
  have h2 : (k : ℝ) ^ k / k.factorial ≤ Real.exp k := Real.pow_div_factorial_le_exp (k : ℝ) hkpos.le k
  have hfac : (0 : ℝ) < k.factorial := by exact_mod_cast Nat.factorial_pos k
  have h3 : (((T + k).choose k : ℕ) : ℝ) ≤ (((T + k : ℕ) : ℝ) / k * Real.exp 1) ^ k := by
    rw [mul_pow, div_pow, ← Real.exp_nat_mul, mul_one]
    calc (((T + k).choose k : ℕ) : ℝ) ≤ ((T + k : ℕ) : ℝ) ^ k / k.factorial := h1
      _ = ((T + k : ℕ) : ℝ) ^ k / (k : ℝ) ^ k * ((k : ℝ) ^ k / k.factorial) := by
          field_simp
      _ ≤ ((T + k : ℕ) : ℝ) ^ k / (k : ℝ) ^ k * Real.exp k := by
          gcongr
  have := Real.log_le_log hCpos h3
  rw [Real.log_pow, Real.log_mul (by positivity) (by positivity), Real.log_exp] at this
  have e : ((T + k : ℕ) : ℝ) / k = (T : ℝ) / k + 1 := by
    push_cast; field_simp
  rw [e] at this
  exact this

theorem chart_sum_aux {d : ℕ} (hd : 1 ≤ d) (y : Fin (d - 1) → ℝ) :
    ∑ i, chartPortfolio d y i = 1 := by
  obtain ⟨n, rfl⟩ : ∃ n, d = n + 1 := ⟨d - 1, by omega⟩
  rw [Fin.sum_univ_castSucc]
  simp [chartPortfolio]

theorem chart_mem_aux {d : ℕ} (hd : 1 ≤ d) (y : Fin (d - 1) → ℝ) (hy : y ∈ chartDomain d) :
    chartPortfolio d y ∈ stdSimplex ℝ (Fin d) := by
  refine ⟨fun i => ?_, chart_sum_aux hd y⟩
  obtain ⟨h0, h1⟩ := hy
  unfold chartPortfolio
  split_ifs
  · exact h0 _
  · linarith

theorem chart_pos_aux {d : ℕ} (hd : 1 ≤ d) (y : Fin (d - 1) → ℝ) (h0 : ∀ k, 0 < y k)
    (h1 : ∑ k, y k < 1) (i : Fin d) : 0 < chartPortfolio d y i := by
  unfold chartPortfolio
  split_ifs
  · exact h0 _
  · linarith

theorem typeClass_one_card {d : ℕ} (j : Fin 1 → Fin d) :
    (typeClass (d := d) (T := 1) (sequenceType j)).card = 1 := by
  rw [Finset.card_eq_one]
  refine ⟨j, ?_⟩
  ext j'
  simp only [typeClass, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
  constructor
  · intro h
    have := congrFun h (j' 0)
    funext t
    fin_cases t
    by_contra hne
    simp [sequenceType] at this
    have hne' : ¬ j 0 = j' 0 := fun h => hne (by simpa using h.symm)
    rw [Finset.filter_singleton, Finset.filter_singleton, if_pos rfl, if_neg hne'] at this
    simp at this
  · rintro rfl; rfl

theorem uniformPrior_compl_aux {d : ℕ} (hd : 1 ≤ d) :
    uniformPrior d (stdSimplex ℝ (Fin d))ᶜ = 0 := by
  have hS : MeasurableSet (stdSimplex ℝ (Fin d)) := (isClosed_stdSimplex ℝ (Fin d)).measurableSet
  rw [uniformPrior, Measure.map_apply (measurable_chartPortfolio d) hS.compl,
    Measure.smul_apply, Measure.restrict_apply ((measurable_chartPortfolio d) hS.compl)]
  have : chartPortfolio d ⁻¹' (stdSimplex ℝ (Fin d))ᶜ ∩ chartDomain d = ∅ := by
    ext y
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_compl_iff, Set.mem_empty_iff_false,
      iff_false, not_and]
    intro h1 h2
    exact h1 (chart_mem_aux hd y h2)
  rw [this]; simp

theorem monomial_eq_aux {d T : ℕ} (j : Fin T → Fin d) (u : Fin d → ℝ) :
    sequenceMonomial j u =
      ∏ i, u i ^ ((Finset.univ.filter (fun t : Fin T => j t = i)).card) := by
  unfold sequenceMonomial
  rw [← Fintype.prod_fiberwise' j u]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_subtype]

theorem count_sum_aux {d T : ℕ} (j : Fin T → Fin d) :
    ∑ i, ((Finset.univ.filter (fun t : Fin T => j t = i)).card : ℝ) = T := by
  have := Finset.card_eq_sum_card_fiberwise (s := (Finset.univ : Finset (Fin T)))
    (t := (Finset.univ : Finset (Fin d))) (f := j) (fun _ _ => Finset.mem_univ _)
  rw [Finset.card_univ, Fintype.card_fin] at this
  exact_mod_cast this.symm

theorem key_aux {d T : ℕ} (hd : 2 ≤ d) (hT : 1 ≤ T) (j : Fin T → Fin d)
    (u : Fin d → ℝ) (hu : u ∈ stdSimplex ℝ (Fin d)) :
    sequenceMonomial j u * ((typeClass (d := d) (T := T) (sequenceType j)).card : ℝ) ≤ 1 := by
  have hTpos : (0 : ℝ) < T := by exact_mod_cast hT
  set N : Fin d → ℝ := fun i => ((Finset.univ.filter (fun t : Fin T => j t = i)).card : ℝ)
    with hN
  have hN0 : ∀ i, 0 ≤ N i := fun i => by positivity
  have h103 := lemma_10_3 hT N hN0 (count_sum_aux j) u hu
  have h104 := theorem_10_4 hd hT (sequenceType j) ⟨j, rfl⟩
  have hmono : sequenceMonomial j u = ∏ i, u i ^ N i := by
    rw [monomial_eq_aux]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [hN, Real.rpow_natCast]
  have hst : ∀ i, sequenceType j i = N i / T := fun i => rfl
  have ha : ∀ i, 0 < (N i / T) ^ N i := by
    intro i
    rcases (hN0 i).lt_or_eq with h | h
    · exact Real.rpow_pos_of_pos (div_pos h hTpos) _
    · rw [← h]; simp
  have h104' : ((typeClass (d := d) (T := T) (sequenceType j)).card : ℝ) ≤
      ∏ i, ((N i / T) ^ N i)⁻¹ := by
    refine h104.trans (le_of_eq (Finset.prod_congr rfl fun i _ => ?_))
    rw [hst, show -(N i / T) * T = -N i by field_simp, Real.rpow_neg (div_nonneg (hN0 i) hTpos.le)]
  rw [hmono]
  have hL0 : 0 ≤ ∏ i, u i ^ N i := Finset.prod_nonneg fun i _ => Real.rpow_nonneg (hu.1 i) _
  calc (∏ i, u i ^ N i) * ((typeClass (d := d) (T := T) (sequenceType j)).card : ℝ)
      ≤ (∏ i, (N i / T) ^ N i) * ∏ i, ((N i / T) ^ N i)⁻¹ :=
        mul_le_mul h103 h104' (by positivity) (Finset.prod_nonneg fun i _ => (ha i).le)
    _ = 1 := by
        rw [← Finset.prod_mul_distrib]
        exact Finset.prod_eq_one fun i _ => mul_inv_cancel₀ (ha i).ne'

theorem solution {d T : ℕ} (hd : 2 ≤ d) (hT : 1 ≤ T)
    (w : ℕ → Fin d → ℝ)
    (hw_nonneg : ∀ t ∈ Finset.Icc 1 T, ∀ i, 0 ≤ w t i)
    (hw_ne : ∀ t ∈ Finset.Icc 1 T, w t ≠ 0) :
    0 < portfolioWealth w (weightedPortfolio (uniformPrior d) w) T ∧
    (∀ u ∈ stdSimplex ℝ (Fin d), 0 < wealthCRP w u T →
      Real.log (wealthCRP w u T) -
        Real.log (portfolioWealth w (weightedPortfolio (uniformPrior d) w) T) ≤
          Real.log (((T + d - 1).choose (d - 1) : ℕ) : ℝ)) ∧
    Real.log (((T + d - 1).choose (d - 1) : ℕ) : ℝ) ≤
      ((d - 1 : ℕ) : ℝ) *
        (Real.log ((T : ℝ) / ((d - 1 : ℕ) : ℝ) + 1) + 1) := by
  have hd1 : 1 ≤ d := by omega
  -- the prior lives on the simplex
  have hFc : uniformPrior d (stdSimplex ℝ (Fin d))ᶜ = 0 := uniformPrior_compl_aux hd1
  have hae : ∀ᵐ p ∂(uniformPrior d), p ∈ stdSimplex ℝ (Fin d) := by
    rw [ae_iff]; exact hFc
  -- monomial integrals
  have hCpos : ∀ m : ℕ, (0 : ℝ) < (((m + d - 1).choose (d - 1) : ℕ) : ℝ) := fun m => by
    exact_mod_cast Nat.choose_pos (by omega)
  have hcard : ∀ m : ℕ, ∀ j : Fin m → Fin d,
      (0 : ℝ) < ((typeClass (d := d) (T := m) (sequenceType j)).card : ℝ) := by
    intro m j
    have : j ∈ typeClass (d := d) (T := m) (sequenceType j) := by simp [typeClass]
    exact_mod_cast Finset.card_pos.mpr ⟨j, this⟩
  -- probability measure
  have hcoord : ∀ i : Fin d, ∫ p, p i ∂(uniformPrior d) = 1 / (d : ℝ) := by
    intro i
    have h := eq_10_5 hd le_rfl (fun _ : Fin 1 => i)
    rw [typeClass_one_card] at h
    have e1 : (fun p : Fin d → ℝ => sequenceMonomial (fun _ : Fin 1 => i) p) = fun p => p i := by
      funext p; simp [sequenceMonomial]
    rw [e1] at h
    rw [h]
    have : (1 + d - 1).choose (d - 1) = d := by
      rw [show 1 + d - 1 = d by omega, Nat.choose_symm_of_eq_add (show d = (d - 1) + 1 by omega)]
      simp
    rw [this]; simp
  have hprob : IsProbabilityMeasure (uniformPrior d) := by
    have hint : ∀ i : Fin d, Integrable (fun p : Fin d → ℝ => p i) (uniformPrior d) := fun i =>
      Integrable.of_integral_ne_zero (by rw [hcoord i]; positivity)
    have h1 : ∫ p, (1 : ℝ) ∂(uniformPrior d) = 1 := by
      have : (fun _ : Fin d → ℝ => (1 : ℝ)) =ᵐ[uniformPrior d] fun p => ∑ i, p i := by
        filter_upwards [hae] with p hp
        exact hp.2.symm
      rw [integral_congr_ae this, integral_finsetSum _ fun i _ => hint i]
      simp only [hcoord, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      have : (d : ℝ) ≠ 0 := by positivity
      field_simp
    rw [integral_const, smul_eq_mul, mul_one] at h1
    constructor
    by_contra hne
    have : uniformPrior d Set.univ ≠ ⊤ := by
      intro htop
      simp [Measure.real, htop] at h1
    apply hne
    rw [Measure.real] at h1
    exact (ENNReal.toReal_eq_one_iff _).mp h1
  have hcont : ∀ t, Continuous (fun p : Fin d → ℝ => wealthBefore w p t) := by
    intro t; unfold wealthBefore; fun_prop
  have hden : ∀ t ∈ Finset.Icc 1 T, 0 < ∫ p, wealthBefore w p t ∂(uniformPrior d) := by
    intro t ht
    have ht' := Finset.mem_Icc.mp ht
    have hs : ∀ s ∈ Finset.Ico 1 t, s ∈ Finset.Icc 1 T := by
      intro s hs; rw [Finset.mem_Ico] at hs; rw [Finset.mem_Icc]; omega
    have hnn : ∀ p ∈ stdSimplex ℝ (Fin d), 0 ≤ wealthBefore w p t := by
      intro p hp
      exact Finset.prod_nonneg fun s hs' => Finset.sum_nonneg fun i _ =>
        mul_nonneg (hw_nonneg s (hs s hs') i) (hp.1 i)
    have hint : Integrable (fun p => wealthBefore w p t) (uniformPrior d) := by
      refine Integrable.of_bound (hcont t).aestronglyMeasurable
        (∏ s ∈ Finset.Ico 1 t, ∑ i, |w s i|) ?_
      filter_upwards [hae] with p hp
      rw [Real.norm_eq_abs, wealthBefore, Finset.abs_prod]
      refine Finset.prod_le_prod (fun _ _ => abs_nonneg _) fun s hs' => ?_
      refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
      rw [abs_mul]
      have h1 : |p i| ≤ 1 := by
        rw [abs_of_nonneg (hp.1 i)]
        rw [← hp.2]; exact Finset.single_le_sum (fun k _ => hp.1 k) (Finset.mem_univ i)
      calc |w s i| * |p i| ≤ |w s i| * 1 := mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
        _ = |w s i| := mul_one _
    rw [integral_pos_iff_support_of_nonneg_ae
      (by filter_upwards [hae] with p hp; exact hnn p hp) hint]
    have hopen : IsOpen (Function.support fun p => wealthBefore w p t) :=
      (hcont t).isOpen_support
    rw [uniformPrior, Measure.map_apply (measurable_chartPortfolio d) hopen.measurableSet,
      Measure.smul_apply,
      Measure.restrict_apply ((measurable_chartPortfolio d) hopen.measurableSet)]
    set U : Set (Fin (d - 1) → ℝ) := {y | (∀ k, 0 < y k) ∧ ∑ k, y k < 1} with hU
    have hUopen : IsOpen U := by
      have : U = (⋂ k, {y : Fin (d-1) → ℝ | 0 < y k}) ∩ {y | ∑ k, y k < 1} := by
        ext y; simp [U]
      rw [this]
      exact (isOpen_iInter_of_finite fun k =>
        isOpen_lt continuous_const (continuous_apply k)).inter
        (isOpen_lt (by fun_prop) continuous_const)
    have hUne : U.Nonempty := by
      refine ⟨fun _ => 1 / (2 * d), fun k => by positivity, ?_⟩
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      have : ((d - 1 : ℕ) : ℝ) < d := by
        have : d - 1 < d := by omega
        exact_mod_cast this
      have hdpos : (0:ℝ) < d := by positivity
      rw [mul_one_div, div_lt_one (by positivity)]
      linarith
    have hUsub : U ⊆ chartPortfolio d ⁻¹' (Function.support fun p => wealthBefore w p t) ∩
        chartDomain d := by
      intro y hy
      refine ⟨?_, fun k => (hy.1 k).le, hy.2.le⟩
      simp only [Set.mem_preimage, Function.mem_support]
      have hpos := chart_pos_aux hd1 y hy.1 hy.2
      apply ne_of_gt
      apply Finset.prod_pos
      intro s hs'
      obtain ⟨i, hi⟩ := Function.ne_iff.mp (hw_ne s (hs s hs'))
      have hwi : 0 < w s i := lt_of_le_of_ne (hw_nonneg s (hs s hs') i) (Ne.symm hi)
      calc 0 < w s i * chartPortfolio d y i := mul_pos hwi (hpos i)
        _ ≤ ∑ i, w s i * chartPortfolio d y i :=
          Finset.single_le_sum (f := fun i => w s i * chartPortfolio d y i)
            (fun k _ => mul_nonneg (hw_nonneg s (hs s hs') k) (hpos k).le) (Finset.mem_univ i)
    have hmp := hUopen.measure_pos volume hUne
    have hfac : (0 : ENNReal) < (Nat.factorial (d - 1) : ENNReal) := by
      exact_mod_cast Nat.factorial_pos _
    rw [smul_eq_mul]
    exact ENNReal.mul_pos hfac.ne' (lt_of_lt_of_le hmp (measure_mono hUsub)).ne'
  have hbound : ∀ u ∈ stdSimplex ℝ (Fin d),
      ENNReal.ofReal (wealthCRP w u T) /
        ENNReal.ofReal (portfolioWealth w (weightedPortfolio (uniformPrior d) w) T) ≤
      ENNReal.ofReal (((T + d - 1).choose (d - 1) : ℕ) : ℝ) := by
    intro u hu
    refine (lemma_10_6 hd hT (uniformPrior d) hFc w hw_nonneg hw_ne hden u hu).trans
      (iSup_le fun j => ?_)
    have hI := eq_10_5 hd hT j
    have hC := hCpos T
    have hK := hcard T j
    have hIpos : 0 < ∫ p, sequenceMonomial j p ∂(uniformPrior d) := by
      rw [hI]; positivity
    rw [← ENNReal.ofReal_div_of_pos hIpos]
    apply ENNReal.ofReal_le_ofReal
    rw [hI]
    have hk := key_aux hd hT j u hu
    rw [show sequenceMonomial j u / (1 / (((T + d - 1).choose (d - 1) : ℕ) : ℝ) /
        ((typeClass (d := d) (T := T) (sequenceType j)).card : ℝ)) =
        sequenceMonomial j u * ((typeClass (d := d) (T := T) (sequenceType j)).card : ℝ) *
          (((T + d - 1).choose (d - 1) : ℕ) : ℝ) by field_simp]
    calc _ ≤ 1 * (((T + d - 1).choose (d - 1) : ℕ) : ℝ) := mul_le_mul_of_nonneg_right hk hC.le
      _ = _ := one_mul _
  have hround : ∀ t ∈ Finset.Icc 1 T, ∀ u : Fin d → ℝ, (∀ i, 0 < u i) →
      0 < ∑ i, w t i * u i := by
    intro t ht u hu
    obtain ⟨i, hi⟩ := Function.ne_iff.mp (hw_ne t ht)
    have hwi : 0 < w t i := lt_of_le_of_ne (hw_nonneg t ht i) (Ne.symm hi)
    calc 0 < w t i * u i := mul_pos hwi (hu i)
      _ ≤ ∑ i, w t i * u i :=
        Finset.single_le_sum (f := fun i => w t i * u i)
          (fun k _ => mul_nonneg (hw_nonneg t ht k) (hu k).le) (Finset.mem_univ i)
  have hdpos : (0 : ℝ) < d := by have : 0 < d := by omega
                                 exact_mod_cast this
  have hu0 : (fun _ : Fin d => 1 / (d : ℝ)) ∈ stdSimplex ℝ (Fin d) := by
    refine ⟨fun _ => by positivity, ?_⟩
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
  have hW0 : 0 < wealthCRP w (fun _ : Fin d => 1 / (d : ℝ)) T :=
    Finset.prod_pos fun t ht => hround t ht _ fun _ => by positivity
  have hWpos : 0 < portfolioWealth w (weightedPortfolio (uniformPrior d) w) T := by
    by_contra hle
    push Not at hle
    have h := hbound _ hu0
    rw [ENNReal.ofReal_of_nonpos hle, ENNReal.div_zero (ENNReal.ofReal_pos.mpr hW0).ne'] at h
    exact ENNReal.ofReal_ne_top (top_le_iff.mp h)
  refine ⟨hWpos, fun u hu hWu => ?_, binom_bound_aux hd⟩
  have h := hbound u hu
  rw [← ENNReal.ofReal_div_of_pos hWpos,
    ENNReal.ofReal_le_ofReal_iff (hCpos T).le] at h
  rw [← Real.log_div hWu.ne' hWpos.ne']
  exact Real.log_le_log (div_pos hWu hWpos) h
