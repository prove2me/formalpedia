-- Prove2me | solution 1 for GradErrors.Stochastic.lemma_2
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-06T00:21:17.685763+00:00
-- url     : https://prove2.me/submissions/b6cde3b8-6076-439b-b828-631840e212b5

import Mathlib

open Filter Topology NNReal ENNReal MeasureTheory ProbabilityTheory InnerProductSpace


namespace GradErrors.Stochastic

lemma mart_conv_aux {Ω : Type*} {m0 : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    (ℱ : Filtration ℕ m0) (d : ℕ → Ω → ℝ)
    (hdm : ∀ t, StronglyMeasurable[ℱ (t + 1)] (d t))
    (hd2 : ∀ t, Integrable (fun ω => d t ω ^ 2) P)
    (hd0 : ∀ t, P[d t | ℱ t] =ᵐ[P] 0)
    (C : ℕ → ℝ) (hC : Summable C) (hdC : ∀ t, ∫ ω, d t ω ^ 2 ∂P ≤ C t) :
    ∀ᵐ ω ∂P, ∃ c, Tendsto (fun T => ∑ t ∈ Finset.range T, d t ω) atTop (𝓝 c) := by
  have hdi : ∀ t, Integrable (d t) P := fun t =>
    ((memLp_two_iff_integrable_sq (((hdm t).mono (ℱ.le _)).aestronglyMeasurable)).2
      (hd2 t)).integrable one_le_two
  set M : ℕ → Ω → ℝ := fun T ω => ∑ t ∈ Finset.range T, d t ω with hM
  have hMm : ∀ T, StronglyMeasurable[ℱ T] (M T) := by
    intro T
    have h := Finset.stronglyMeasurable_sum (Finset.range T) (f := d)
      (fun t ht => (hdm t).mono (ℱ.mono (show t + 1 ≤ T by have := Finset.mem_range.1 ht; omega)))
    have he : M T = ∑ t ∈ Finset.range T, d t := by
      funext ω; simp [M, Finset.sum_apply]
    rw [he]; exact h
  have hMi : ∀ T, Integrable (M T) P := fun T => integrable_finsetSum _ (fun t _ => hdi t)
  have hmart : Martingale M ℱ P := by
    refine martingale_of_condExp_sub_eq_zero_nat hMm hMi (fun i => ?_)
    have : M (i + 1) - M i = d i := by
      funext ω; simp [M, Finset.sum_range_succ]
    rw [this]; exact hd0 i
  have hsq : ∀ T, Integrable (fun ω => M T ω ^ 2) P ∧
      ∫ ω, M T ω ^ 2 ∂P ≤ ∑ t ∈ Finset.range T, C t := by
    intro T
    induction T with
    | zero => simp [M]
    | succ T ih =>
      obtain ⟨hi, hb⟩ := ih
      have hMd : Integrable (fun ω => M T ω * d T ω) P := by
        refine Integrable.mono' (hi.add (hd2 T))
          ((hMi T).aestronglyMeasurable.mul (hdi T).aestronglyMeasurable)
          (ae_of_all _ fun ω => ?_)
        simp only [Pi.add_apply, Real.norm_eq_abs, abs_mul]
        nlinarith [abs_nonneg (M T ω), abs_nonneg (d T ω), sq_abs (M T ω), sq_abs (d T ω)]
      have h0 : ∫ ω, M T ω * d T ω ∂P = 0 := by
        have h1 := condExp_mul_of_stronglyMeasurable_left (μ := P) (hMm T) hMd (hdi T)
        calc ∫ ω, M T ω * d T ω ∂P = ∫ ω, (P[M T * d T | ℱ T]) ω ∂P :=
              (integral_condExp (ℱ.le T)).symm
          _ = ∫ ω, (M T * P[d T | ℱ T]) ω ∂P := integral_congr_ae h1
          _ = ∫ ω, (0 : ℝ) ∂P := by
              refine integral_congr_ae ?_
              filter_upwards [hd0 T] with ω h
              simp [h]
          _ = 0 := by simp
      have hexp : (fun ω => M (T + 1) ω ^ 2) =
          fun ω => (M T ω ^ 2 + 2 * (M T ω * d T ω)) + d T ω ^ 2 := by
        funext ω; simp only [M, Finset.sum_range_succ]; ring
      rw [hexp]
      have hA : Integrable (fun ω => M T ω ^ 2 + 2 * (M T ω * d T ω)) P := hi.add (hMd.const_mul 2)
      refine ⟨hA.add (hd2 T), ?_⟩
      rw [integral_add hA (hd2 T), integral_add hi (hMd.const_mul 2),
        integral_const_mul, h0, Finset.sum_range_succ]
      linarith [hdC T]
  have hC0 : ∀ t, 0 ≤ C t := fun t => le_trans (integral_nonneg fun ω => sq_nonneg _) (hdC t)
  have hbdd : ∀ T, eLpNorm (M T) 1 P ≤ ((Real.toNNReal (1 + ∑' t, C t) : ℝ≥0) : ℝ≥0∞) := by
    intro T
    rw [eLpNorm_one_eq_lintegral_enorm]
    have hint : Integrable (fun ω => 1 + M T ω ^ 2) P := (integrable_const 1).add (hsq T).1
    calc ∫⁻ ω, ‖M T ω‖ₑ ∂P ≤ ∫⁻ ω, ENNReal.ofReal (1 + M T ω ^ 2) ∂P := by
          refine lintegral_mono fun ω => ?_
          rw [← ofReal_norm]
          apply ENNReal.ofReal_le_ofReal
          rw [Real.norm_eq_abs]
          nlinarith [abs_nonneg (M T ω), sq_abs (M T ω)]
      _ = ENNReal.ofReal (∫ ω, 1 + M T ω ^ 2 ∂P) :=
          (ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ fun ω => by positivity)).symm
      _ ≤ ENNReal.ofReal (1 + ∑' t, C t) := by
          apply ENNReal.ofReal_le_ofReal
          rw [integral_add (integrable_const 1) (hsq T).1]
          simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
          linarith [(hsq T).2, hC.sum_le_tsum (Finset.range T) (fun t _ => hC0 t)]
  exact hmart.submartingale.exists_ae_tendsto_of_bdd hbdd

theorem lemma2_core {Ω : Type*} {m0 : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    (ℱ : Filtration ℕ m0) {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ F] (γ : ℕ → ℝ) (hsq : Summable (fun t => γ t ^ 2))
    (r : ℕ → Ω → F) (B : ℝ)
    (hrm : ∀ t, StronglyMeasurable[ℱ (t + 1)] (r t))
    (hr2 : ∀ t, Integrable (fun ω => ‖r t ω‖ ^ 2) P)
    (hr0 : ∀ t, P[r t | ℱ t] =ᵐ[P] 0)
    (hrB : ∀ t, P[fun ω => ‖r t ω‖ ^ 2 | ℱ t] ≤ᵐ[P] fun _ => B) :
    ∀ᵐ ω ∂P,
      (∃ S : F, Tendsto (fun T => ∑ t ∈ Finset.range (T + 1), γ t • r t ω) atTop (𝓝 S)) ∧
      (∃ S' : ℝ,
        Tendsto (fun T => ∑ t ∈ Finset.range (T + 1), γ t ^ 2 * ‖r t ω‖ ^ 2) atTop (𝓝 S')) := by
  have hEr : ∀ t, ∫ ω, ‖r t ω‖ ^ 2 ∂P ≤ B := by
    intro t
    rw [← integral_condExp (ℱ.le t)]
    calc _ ≤ ∫ ω, B ∂P := integral_mono_ae integrable_condExp (integrable_const B) (hrB t)
      _ = B := by simp
  have hB : 0 ≤ B := le_trans (integral_nonneg fun ω => by positivity) (hEr 0)
  have hrmeas : ∀ t, AEStronglyMeasurable (r t) P := fun t =>
    ((hrm t).mono (ℱ.le _)).aestronglyMeasurable
  have hri : ∀ t, Integrable (r t) P := by
    intro t
    refine Integrable.mono' ((integrable_const (1 : ℝ)).add (hr2 t)) (hrmeas t)
      (ae_of_all _ fun ω => ?_)
    simp only [Pi.add_apply]
    nlinarith [norm_nonneg (r t ω)]
  -- part 2
  have part2 : ∀ᵐ ω ∂P, Summable (fun t => γ t ^ 2 * ‖r t ω‖ ^ 2) := by
    have hmeas : ∀ t, AEMeasurable (fun ω => ENNReal.ofReal (γ t ^ 2 * ‖r t ω‖ ^ 2)) P :=
      fun t => ((hr2 t).const_mul (γ t ^ 2)).aestronglyMeasurable.aemeasurable.ennreal_ofReal
    have hlt : ∫⁻ ω, ∑' t, ENNReal.ofReal (γ t ^ 2 * ‖r t ω‖ ^ 2) ∂P ≠ ∞ := by
      rw [lintegral_tsum hmeas]
      refine (lt_of_le_of_lt ?_ (ENNReal.ofReal_lt_top (r := ∑' t, γ t ^ 2 * B))).ne
      calc ∑' t, ∫⁻ ω, ENNReal.ofReal (γ t ^ 2 * ‖r t ω‖ ^ 2) ∂P
            = ∑' t, ENNReal.ofReal (γ t ^ 2 * ∫ ω, ‖r t ω‖ ^ 2 ∂P) := by
              congr 1; funext t
              rw [← integral_const_mul, ofReal_integral_eq_lintegral_ofReal
                ((hr2 t).const_mul _) (ae_of_all _ fun ω => by positivity)]
        _ ≤ ∑' t, ENNReal.ofReal (γ t ^ 2 * B) := ENNReal.tsum_le_tsum fun t =>
              ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left (hEr t) (sq_nonneg _))
        _ = ENNReal.ofReal (∑' t, γ t ^ 2 * B) :=
              (ENNReal.ofReal_tsum_of_nonneg (fun t => by positivity) (hsq.mul_right B)).symm
    filter_upwards [ae_lt_top' (AEMeasurable.ennreal_tsum hmeas) hlt] with ω hω
    have := ENNReal.summable_toReal hω.ne
    refine this.congr fun t => ?_
    rw [ENNReal.toReal_ofReal (by positivity)]
  -- part 1
  let b := stdOrthonormalBasis ℝ F
  have hcoord : ∀ i, ∀ᵐ ω ∂P, ∃ c, Tendsto
      (fun T => ∑ t ∈ Finset.range T, γ t * ⟪b i, r t ω⟫_ℝ) atTop (𝓝 c) := by
    intro i
    have hbound : ∀ t ω, (γ t * ⟪b i, r t ω⟫_ℝ) ^ 2 ≤ γ t ^ 2 * ‖r t ω‖ ^ 2 := by
      intro t ω
      have h1 : |⟪b i, r t ω⟫_ℝ| ≤ ‖r t ω‖ := by
        have := abs_real_inner_le_norm (b i) (r t ω)
        rwa [b.orthonormal.1 i, one_mul] at this
      rw [mul_pow, ← sq_abs ⟪b i, r t ω⟫_ℝ]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg _) h1 2) (sq_nonneg _)
    have hdm : ∀ t, StronglyMeasurable[ℱ (t + 1)] (fun ω => γ t * ⟪b i, r t ω⟫_ℝ) := by
      intro t
      exact stronglyMeasurable_const.mul
        ((innerSL ℝ (b i)).continuous.comp_stronglyMeasurable (hrm t))
    have hd2 : ∀ t, Integrable (fun ω => (γ t * ⟪b i, r t ω⟫_ℝ) ^ 2) P := by
      intro t
      refine Integrable.mono' ((hr2 t).const_mul (γ t ^ 2))
        ((((hdm t).mono (ℱ.le _)).aestronglyMeasurable).pow 2) (ae_of_all _ fun ω => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact hbound t ω
    refine mart_conv_aux P ℱ _ hdm hd2 (fun t => ?_) (fun t => γ t ^ 2 * B) (hsq.mul_right B)
      (fun t => ?_)
    · refine (ae_eq_condExp_of_forall_setIntegral_eq (ℱ.le t) ?_ (fun s _ _ => integrableOn_zero)
        (fun s hs _ => ?_) aestronglyMeasurable_zero).symm
      · exact ((hri t).const_inner (b i)).const_mul (γ t)
      · have h0 : ∫ x in s, r t x ∂P = 0 := by
          rw [← setIntegral_condExp (ℱ.le t) (hri t) hs,
            integral_congr_ae (ae_restrict_of_ae (hr0 t))]
          simp
        rw [integral_const_mul, integral_inner (hri t).integrableOn (b i), h0]
        simp
    · calc ∫ ω, (γ t * ⟪b i, r t ω⟫_ℝ) ^ 2 ∂P ≤ ∫ ω, γ t ^ 2 * ‖r t ω‖ ^ 2 ∂P :=
            integral_mono (hd2 t) ((hr2 t).const_mul _) (fun ω => hbound t ω)
        _ ≤ γ t ^ 2 * B := by
            rw [integral_const_mul]
            exact mul_le_mul_of_nonneg_left (hEr t) (sq_nonneg _)
  filter_upwards [ae_all_iff.2 hcoord, part2] with ω h1 h2
  refine ⟨?_, ⟨_, h2.hasSum.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)⟩⟩
  choose c hc using h1
  refine ⟨∑ i, c i • b i, ?_⟩
  have he : (fun T => ∑ t ∈ Finset.range (T + 1), γ t • r t ω) =
      fun T => ∑ i, (∑ t ∈ Finset.range (T + 1), γ t * ⟪b i, r t ω⟫_ℝ) • b i := by
    funext T
    rw [← b.sum_repr' (∑ t ∈ Finset.range (T + 1), γ t • r t ω)]
    congr 1; funext i
    rw [inner_sum]
    congr 1
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [inner_smul_right]
  rw [he]
  exact tendsto_finset_sum _ fun i _ =>
    ((hc i).comp (tendsto_add_atTop_nat 1)).smul_const (b i)

end GradErrors.Stochastic

open GradErrors.Stochastic


theorem solution {Ω : Type*} {m0 : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    (ℱ : Filtration ℕ m0) {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ F] (γ : ℕ → ℝ) (hsq : Summable (fun t => γ t ^ 2))
    (r : ℕ → Ω → F) (B : ℝ)
    (hrm : ∀ t, StronglyMeasurable[ℱ (t + 1)] (r t))
    (hr2 : ∀ t, Integrable (fun ω => ‖r t ω‖ ^ 2) P)
    (hr0 : ∀ t, P[r t | ℱ t] =ᵐ[P] 0)
    (hrB : ∀ t, P[fun ω => ‖r t ω‖ ^ 2 | ℱ t] ≤ᵐ[P] fun _ => B) :
    ∀ᵐ ω ∂P,
      (∃ S : F, Tendsto (fun T => ∑ t ∈ Finset.range (T + 1), γ t • r t ω) atTop (𝓝 S)) ∧
      (∃ S' : ℝ,
        Tendsto (fun T => ∑ t ∈ Finset.range (T + 1), γ t ^ 2 * ‖r t ω‖ ^ 2) atTop (𝓝 S')) := by
  exact lemma2_core P ℱ γ hsq r B hrm hr2 hr0 hrB
