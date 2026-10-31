-- Prove2me | solution 1 for LiquidDemocracy.Upward.late_bins
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T11:26:31.862227+00:00
-- url     : https://prove2.me/submissions/65717a1c-7ff9-42fd-8ad1-4dd595dd11a3

import Mathlib
import Definitions.Def_LiquidDemocracy_Upward_Urn

open MeasureTheory Filter Topology LiquidDemocracy.Upward

theorem LDL_support (p : ℝ) (k : ℕ) (m : ℕ) :
    wChain p k m {w | m + 1 < w} = 0 := by
  induction m with
  | zero => simp [wChain]
  | succ m ih =>
    simp only [wChain]
    rw [Measure.bind_apply (MeasurableSet.of_discrete) (Measurable.of_discrete).aemeasurable]
    have hae : ∀ᵐ w0 ∂wChain p k m, w0 ≤ m + 1 := by
      rw [ae_iff]; simpa [not_le] using ih
    rw [lintegral_eq_zero_iff (Measurable.of_discrete)]
    filter_upwards [hae] with w0 hw0
    simp only [wStep, Measure.coe_add, Measure.coe_smul, Pi.add_apply, Pi.smul_apply,
      smul_eq_mul, Pi.zero_apply]
    rw [Measure.dirac_apply, Measure.dirac_apply]
    have e1 : ¬ (m + 1 + 1 < w0 + 1) := by omega
    have e2 : ¬ (m + 1 + 1 < w0) := by omega
    simp [Set.indicator, e1, e2]

theorem LDL_mean (p : ℝ) (hp : p ∈ Set.Ioo (0 : ℝ) 1) (k : ℕ) (hk : 1 ≤ k) (m : ℕ) :
    ∫⁻ w, (w : ENNReal) ∂(wChain p k m) =
      ENNReal.ofReal (∏ j ∈ Finset.range m, (1 + p / ((k : ℝ) + j))) := by
  induction m with
  | zero => simp [wChain]
  | succ m ih =>
    simp only [wChain]
    rw [Measure.lintegral_bind (Measurable.of_discrete).aemeasurable
      (Measurable.of_discrete).aemeasurable]
    have hae : ∀ᵐ w0 ∂wChain p k m, w0 ≤ m + 1 := by
      rw [ae_iff]; simpa [not_le] using LDL_support p k m
    have ht : (0 : ℝ) < (k : ℝ) + m := by
      have : (1 : ℝ) ≤ k := by exact_mod_cast hk
      positivity
    have key : ∀ᵐ w0 ∂wChain p k m,
        ∫⁻ w, (w : ENNReal) ∂(wStep p (k + m) w0) =
          ENNReal.ofReal (1 + p / ((k : ℝ) + m)) * (w0 : ENNReal) := by
      filter_upwards [hae] with w0 hw0
      have hw0' : (w0 : ℝ) ≤ (k : ℝ) + m := by
        have : (w0 : ℝ) ≤ (m : ℝ) + 1 := by exact_mod_cast hw0
        have : (1 : ℝ) ≤ k := by exact_mod_cast hk
        linarith
      have h1 : 0 ≤ p * w0 / ((k + m : ℕ) : ℝ) := by
        have := hp.1.le; positivity
      have h2 : p * w0 / ((k + m : ℕ) : ℝ) ≤ 1 := by
        rw [div_le_one (by push_cast; exact ht)]
        push_cast
        nlinarith [hp.2, hp.1, (Nat.cast_nonneg w0 : (0 : ℝ) ≤ w0)]
      simp only [wStep]
      rw [lintegral_add_measure, lintegral_smul_measure, lintegral_smul_measure,
        lintegral_dirac, lintegral_dirac]
      rw [show ((w0 + 1 : ℕ) : ENNReal) = ENNReal.ofReal ((w0 : ℝ) + 1) by
            rw [← ENNReal.ofReal_natCast]; push_cast; rfl,
        show ((w0 : ℕ) : ENNReal) = ENNReal.ofReal (w0 : ℝ) by rw [ENNReal.ofReal_natCast]]
      simp only [smul_eq_mul]
      rw [← ENNReal.ofReal_mul h1, ← ENNReal.ofReal_mul (by linarith),
        ← ENNReal.ofReal_add (by positivity) (by nlinarith),
        ← ENNReal.ofReal_mul (by have := hp.1.le; positivity)]
      congr 1
      push_cast
      field_simp
      ring
    rw [lintegral_congr_ae key, lintegral_const_mul _ (Measurable.of_discrete), ih,
      ← ENNReal.ofReal_mul (by have := hp.1.le; positivity), Finset.prod_range_succ, mul_comm]

/-- `1 + a/x ≤ (x/(x-1))^a` for `x > 1`, `a ≥ 0`. -/
theorem LDL_step_le (a x : ℝ) (ha : 0 ≤ a) (hx : 1 < x) :
    1 + a / x ≤ (x / (x - 1)) ^ a := by
  have hx0 : 0 < x := by linarith
  have hx1 : 0 < x - 1 := by linarith
  have hlog : 1 / x ≤ Real.log (x / (x - 1)) := by
    have h := Real.log_le_sub_one_of_pos (show 0 < (x - 1) / x by positivity)
    have heq : Real.log (x / (x - 1)) = - Real.log ((x - 1) / x) := by
      rw [← Real.log_inv, inv_div]
    rw [heq]
    have : (x - 1) / x - 1 = -(1 / x) := by field_simp; ring
    linarith
  calc 1 + a / x ≤ Real.exp (a / x) := by linarith [Real.add_one_le_exp (a / x)]
    _ ≤ Real.exp (Real.log (x / (x - 1)) * a) := by
        apply Real.exp_le_exp.mpr
        rw [div_eq_mul_one_div, mul_comm]
        exact mul_le_mul_of_nonneg_right hlog ha
    _ = (x / (x - 1)) ^ a := by rw [Real.rpow_def_of_pos (by positivity)]

theorem LDL_prod_le_aux (a : ℝ) (ha : 0 ≤ a) (k : ℕ) (hk : 1 ≤ k) (m : ℕ) :
    ∏ j ∈ Finset.range (m + 1), (1 + a / ((k : ℝ) + j)) ≤
      (1 + a / k) * (((k : ℝ) + m) / k) ^ a := by
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  induction m with
  | zero => simp [div_self (by linarith : (k : ℝ) ≠ 0)]
  | succ m ih =>
    rw [Finset.prod_range_succ]
    have hx : 1 < (k : ℝ) + (m + 1 : ℕ) := by
      push_cast; linarith [(m.cast_nonneg : (0 : ℝ) ≤ m)]
    have hs := LDL_step_le a _ ha hx
    have hpos : 0 ≤ ∏ j ∈ Finset.range (m + 1), (1 + a / ((k : ℝ) + j)) :=
      Finset.prod_nonneg fun j _ => by positivity
    calc (∏ j ∈ Finset.range (m + 1), (1 + a / ((k : ℝ) + j))) * (1 + a / ((k : ℝ) + (m + 1 : ℕ)))
        ≤ ((1 + a / k) * (((k : ℝ) + m) / k) ^ a) *
            (((k : ℝ) + (m + 1 : ℕ)) / ((k : ℝ) + (m + 1 : ℕ) - 1)) ^ a :=
          mul_le_mul ih hs (by positivity) (by positivity)
      _ = (1 + a / k) * (((k : ℝ) + (m + 1 : ℕ)) / k) ^ a := by
          rw [mul_assoc, ← Real.mul_rpow (by positivity) (by
            push_cast; apply div_nonneg <;> linarith [(m.cast_nonneg : (0 : ℝ) ≤ m)])]
          congr 2
          push_cast
          have : (k : ℝ) + m ≠ 0 := by linarith [(m.cast_nonneg : (0 : ℝ) ≤ m)]
          have e : (k : ℝ) + ((m : ℝ) + 1) - 1 = k + m := by ring
          rw [e]
          field_simp

theorem LDL_prod_le (a : ℝ) (ha : 0 ≤ a) (k : ℕ) (hk : 1 ≤ k) (m : ℕ) :
    ∏ j ∈ Finset.range m, (1 + a / ((k : ℝ) + j)) ≤ (1 + a) * (((k : ℝ) + m) / k) ^ a := by
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  rcases m with _ | m
  · simp only [Finset.range_zero, Finset.prod_empty, Nat.cast_zero, add_zero]
    rw [div_self (by linarith), Real.one_rpow]; linarith
  · refine (LDL_prod_le_aux a ha k hk m).trans ?_
    apply mul_le_mul
    · have : a / k ≤ a := div_le_self ha hk'
      linarith
    · apply Real.rpow_le_rpow (by positivity) _ ha
      apply div_le_div_of_nonneg_right _ (by positivity)
      push_cast; linarith
    · positivity
    · positivity

theorem LDL_markov (ν : Measure ℕ) (f : ℕ → ℝ) (M : ℝ) (hM : 0 ≤ M)
    (hI : ∫⁻ w, ENNReal.ofReal (f w) ∂ν = ENNReal.ofReal M) (y : ℝ) (hy : 0 < y) (A : Set ℕ)
    (hA : ∀ w ∈ A, y ≤ f w) : ν.real A ≤ M / y := by
  have h1 : ν A ≤ ν {w | ENNReal.ofReal y ≤ ENNReal.ofReal (f w)} :=
    measure_mono fun w hw => ENNReal.ofReal_le_ofReal (hA w hw)
  have h2 := meas_ge_le_lintegral_div (μ := ν) (f := fun w => ENNReal.ofReal (f w))
    (Measurable.of_discrete).aemeasurable (ε := ENNReal.ofReal y)
    (by simpa using hy) ENNReal.ofReal_ne_top
  rw [hI, ← ENNReal.ofReal_div_of_pos hy] at h2
  rw [measureReal_def]
  have := (h1.trans h2)
  calc (ν A).toReal ≤ (ENNReal.ofReal (M / y)).toReal :=
        ENNReal.toReal_mono ENNReal.ofReal_ne_top this
    _ = M / y := ENNReal.toReal_ofReal (by positivity)


theorem LDL_second (p : ℝ) (hp : p ∈ Set.Ioo (0 : ℝ) 1) (k : ℕ) (hk : 1 ≤ k) (m : ℕ) :
    ∫⁻ w, ENNReal.ofReal ((w : ℝ) * ((w : ℝ) + 1)) ∂(wChain p k m) =
      ENNReal.ofReal (2 * ∏ j ∈ Finset.range m, (1 + 2 * p / ((k : ℝ) + j))) := by
  induction m with
  | zero => simp [wChain]; norm_num
  | succ m ih =>
    simp only [wChain]
    rw [Measure.lintegral_bind (Measurable.of_discrete).aemeasurable
      (Measurable.of_discrete).aemeasurable]
    have hae : ∀ᵐ w0 ∂wChain p k m, w0 ≤ m + 1 := by
      rw [ae_iff]; simpa [not_le] using LDL_support p k m
    have ht : (0 : ℝ) < (k : ℝ) + m := by
      have : (1 : ℝ) ≤ k := by exact_mod_cast hk
      positivity
    have key : ∀ᵐ w0 ∂wChain p k m,
        ∫⁻ w, ENNReal.ofReal ((w : ℝ) * ((w : ℝ) + 1)) ∂(wStep p (k + m) w0) =
          ENNReal.ofReal (1 + 2 * p / ((k : ℝ) + m)) *
            ENNReal.ofReal ((w0 : ℝ) * ((w0 : ℝ) + 1)) := by
      filter_upwards [hae] with w0 hw0
      have hw0' : (w0 : ℝ) ≤ (k : ℝ) + m := by
        have : (w0 : ℝ) ≤ (m : ℝ) + 1 := by exact_mod_cast hw0
        have : (1 : ℝ) ≤ k := by exact_mod_cast hk
        linarith
      have h1 : 0 ≤ p * w0 / ((k + m : ℕ) : ℝ) := by
        have := hp.1.le; positivity
      have h2 : p * w0 / ((k + m : ℕ) : ℝ) ≤ 1 := by
        rw [div_le_one (by push_cast; exact ht)]
        push_cast
        nlinarith [hp.2, hp.1, (Nat.cast_nonneg w0 : (0 : ℝ) ≤ w0)]
      simp only [wStep]
      rw [lintegral_add_measure, lintegral_smul_measure, lintegral_smul_measure,
        lintegral_dirac, lintegral_dirac]
      simp only [smul_eq_mul]
      have hw0n : (0 : ℝ) ≤ w0 := Nat.cast_nonneg w0
      rw [← ENNReal.ofReal_mul h1,
        ← ENNReal.ofReal_mul (p := 1 - p * w0 / ((k + m : ℕ) : ℝ)) (by linarith),
        ← ENNReal.ofReal_add (by positivity) (mul_nonneg (by linarith) (by positivity)),
        ← ENNReal.ofReal_mul (by have := hp.1.le; positivity)]
      congr 1
      push_cast
      field_simp
      ring
    rw [lintegral_congr_ae key, lintegral_const_mul _ (Measurable.of_discrete), ih,
      ← ENNReal.ofReal_mul (by have := hp.1.le; positivity), Finset.prod_range_succ]
    congr 1
    ring

theorem solution (p γ δ : ℝ) (hp : p ∈ Set.Ioo (0 : ℝ) 1) (hγ₁ : 3 / 4 < γ) (hγ₂ : γ < 1)
    (hδ₁ : p + (1 - p) * γ < δ) (hδ₂ : δ < 1) :
    Tendsto (fun T : ℕ => ∑ k ∈ Finset.Ioc ⌊(T : ℝ) ^ γ⌋₊ T,
      (wLaw p k T).real {w | (T : ℝ) ^ δ < (w : ℝ)}) atTop (𝓝 0) := by
  set e : ℝ := (δ + δ) - 1 - (1 - γ) * (2 * p) with he
  have he0 : 0 < e := by rw [he]; nlinarith [hp.1, hp.2]
  have hlim : Tendsto (fun T : ℕ => 6 * (T : ℝ) ^ (-e)) atTop (𝓝 0) := by
    have := ((tendsto_rpow_neg_atTop he0).comp tendsto_natCast_atTop_atTop).const_mul 6
    simpa using this
  apply squeeze_zero' (Eventually.of_forall fun T => Finset.sum_nonneg fun k _ =>
    measureReal_nonneg) _ hlim
  filter_upwards [eventually_ge_atTop 1] with T hT
  have hT1 : (1 : ℝ) ≤ T := by exact_mod_cast hT
  have hT0 : (0 : ℝ) < T := by linarith
  set F := ⌊(T : ℝ) ^ γ⌋₊ with hFdef
  have hTγ0 : 0 < (T : ℝ) ^ γ := by positivity
  have hTδ0 : 0 < (T : ℝ) ^ δ := by positivity
  set B : ℝ := 6 * (T : ℝ) ^ ((1 - γ) * (2 * p)) / ((T : ℝ) ^ δ * (T : ℝ) ^ δ) with hB
  have hB0 : 0 ≤ B := by positivity
  have hterm : ∀ k ∈ Finset.Ioc F T, (wLaw p k T).real {w | (T : ℝ) ^ δ < (w : ℝ)} ≤ B := by
    intro k hk
    obtain ⟨hFk, hkT⟩ := Finset.mem_Ioc.mp hk
    have hk1 : 1 ≤ k := by omega
    have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk1
    have hk0 : (0 : ℝ) < k := by linarith
    have hγk : (T : ℝ) ^ γ ≤ k := by
      have h1 := Nat.lt_floor_add_one ((T : ℝ) ^ γ)
      have h2 : ((F + 1 : ℕ) : ℝ) ≤ k := by exact_mod_cast hFk
      push_cast at h2
      rw [← hFdef] at h1
      linarith
    simp only [wLaw, if_pos hkT]
    have hM := LDL_markov (wChain p k (T - k)) (fun w => (w : ℝ) * ((w : ℝ) + 1)) _
      (mul_nonneg (by norm_num) (Finset.prod_nonneg fun j _ => by
        have := hp.1.le; positivity))
      (LDL_second p hp k hk1 (T - k)) ((T : ℝ) ^ δ * (T : ℝ) ^ δ) (by positivity)
      {w | (T : ℝ) ^ δ < (w : ℝ)} (fun w hw => by
        simp only [Set.mem_setOf_eq] at hw
        have : (0 : ℝ) ≤ w := Nat.cast_nonneg w
        nlinarith)
    refine hM.trans ?_
    have hprod := LDL_prod_le (2 * p) (by linarith [hp.1]) k hk1 (T - k)
    have hkm : (k : ℝ) + ((T - k : ℕ) : ℝ) = T := by
      rw [Nat.cast_sub hkT]; ring
    rw [hkm] at hprod
    have hTk : (T : ℝ) / k ≤ (T : ℝ) ^ (1 - γ) := by
      rw [Real.rpow_sub hT0, Real.rpow_one]
      exact div_le_div_of_nonneg_left hT0.le hTγ0 hγk
    have hpow : ((T : ℝ) / k) ^ (2 * p) ≤ (T : ℝ) ^ ((1 - γ) * (2 * p)) := by
      rw [Real.rpow_mul hT0.le]
      exact Real.rpow_le_rpow (by positivity) hTk (by linarith [hp.1])
    rw [hB]
    apply div_le_div_of_nonneg_right _ (by positivity)
    calc 2 * ∏ j ∈ Finset.range (T - k), (1 + 2 * p / ((k : ℝ) + j))
        ≤ 2 * ((1 + 2 * p) * ((T : ℝ) / k) ^ (2 * p)) := by linarith
      _ ≤ 2 * (3 * (T : ℝ) ^ ((1 - γ) * (2 * p))) := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          apply mul_le_mul (by linarith [hp.2]) hpow (by positivity) (by norm_num)
      _ = 6 * (T : ℝ) ^ ((1 - γ) * (2 * p)) := by ring
  calc ∑ k ∈ Finset.Ioc F T, (wLaw p k T).real {w | (T : ℝ) ^ δ < (w : ℝ)}
      ≤ (Finset.Ioc F T).card • B := Finset.sum_le_card_nsmul _ _ _ hterm
    _ = ((T - F : ℕ) : ℝ) * B := by rw [nsmul_eq_mul, Nat.card_Ioc]
    _ ≤ (T : ℝ) * B := by
        apply mul_le_mul_of_nonneg_right _ hB0
        exact_mod_cast Nat.sub_le T F
    _ = 6 * (T : ℝ) ^ (-e) := by
        rw [hB, he]
        have : -((δ + δ) - 1 - (1 - γ) * (2 * p)) = (1 + (1 - γ) * (2 * p)) - (δ + δ) := by ring
        rw [this, Real.rpow_sub hT0, Real.rpow_add hT0, Real.rpow_add hT0, Real.rpow_one]
        field_simp
