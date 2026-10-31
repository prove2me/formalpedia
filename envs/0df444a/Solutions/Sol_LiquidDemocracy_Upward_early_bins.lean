-- Prove2me | solution 1 for LiquidDemocracy.Upward.early_bins
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T11:23:32.393281+00:00
-- url     : https://prove2.me/submissions/50f4bd43-9843-4a0e-84aa-9b8a34cfa2ab

import Mathlib
import Definitions.Def_LiquidDemocracy_Upward_Urn

open MeasureTheory Filter Topology LiquidDemocracy.Upward

theorem LDE_support (p : ℝ) (k : ℕ) (m : ℕ) :
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

theorem LDE_mean (p : ℝ) (hp : p ∈ Set.Ioo (0 : ℝ) 1) (k : ℕ) (hk : 1 ≤ k) (m : ℕ) :
    ∫⁻ w, (w : ENNReal) ∂(wChain p k m) =
      ENNReal.ofReal (∏ j ∈ Finset.range m, (1 + p / ((k : ℝ) + j))) := by
  induction m with
  | zero => simp [wChain]
  | succ m ih =>
    simp only [wChain]
    rw [Measure.lintegral_bind (Measurable.of_discrete).aemeasurable
      (Measurable.of_discrete).aemeasurable]
    have hae : ∀ᵐ w0 ∂wChain p k m, w0 ≤ m + 1 := by
      rw [ae_iff]; simpa [not_le] using LDE_support p k m
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
theorem LDE_step_le (a x : ℝ) (ha : 0 ≤ a) (hx : 1 < x) :
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

theorem LDE_prod_le_aux (a : ℝ) (ha : 0 ≤ a) (k : ℕ) (hk : 1 ≤ k) (m : ℕ) :
    ∏ j ∈ Finset.range (m + 1), (1 + a / ((k : ℝ) + j)) ≤
      (1 + a / k) * (((k : ℝ) + m) / k) ^ a := by
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  induction m with
  | zero => simp [div_self (by linarith : (k : ℝ) ≠ 0)]
  | succ m ih =>
    rw [Finset.prod_range_succ]
    have hx : 1 < (k : ℝ) + (m + 1 : ℕ) := by
      push_cast; linarith [(m.cast_nonneg : (0 : ℝ) ≤ m)]
    have hs := LDE_step_le a _ ha hx
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

theorem LDE_prod_le (a : ℝ) (ha : 0 ≤ a) (k : ℕ) (hk : 1 ≤ k) (m : ℕ) :
    ∏ j ∈ Finset.range m, (1 + a / ((k : ℝ) + j)) ≤ (1 + a) * (((k : ℝ) + m) / k) ^ a := by
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  rcases m with _ | m
  · simp only [Finset.range_zero, Finset.prod_empty, Nat.cast_zero, add_zero]
    rw [div_self (by linarith), Real.one_rpow]; linarith
  · refine (LDE_prod_le_aux a ha k hk m).trans ?_
    apply mul_le_mul
    · have : a / k ≤ a := div_le_self ha hk'
      linarith
    · apply Real.rpow_le_rpow (by positivity) _ ha
      apply div_le_div_of_nonneg_right _ (by positivity)
      push_cast; linarith
    · positivity
    · positivity

theorem LDE_markov (ν : Measure ℕ) (f : ℕ → ℝ) (M : ℝ) (hM : 0 ≤ M)
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

theorem LDE_sum_rpow (p : ℝ) (hp : p ∈ Set.Ioo (0 : ℝ) 1) (F : ℕ) :
    ∑ k ∈ Finset.Icc 1 F, (k : ℝ) ^ (-p) ≤ (F : ℝ) ^ (1 - p) / (1 - p) := by
  have h1p : 0 < 1 - p := by linarith [hp.2]
  induction F with
  | zero => simp [Real.zero_rpow (by linarith : (1 - p) ≠ 0)]
  | succ F ih =>
    rw [Finset.sum_Icc_succ_top (by omega)]
    set y : ℝ := ((F + 1 : ℕ) : ℝ) with hy
    have hy1 : (1 : ℝ) ≤ y := by rw [hy]; push_cast; linarith [(F.cast_nonneg : (0 : ℝ) ≤ F)]
    have hy0 : 0 < y := by linarith
    have hF : (F : ℝ) = y * (1 + -1 / y) := by rw [hy]; push_cast; field_simp; ring
    have hs : -1 ≤ -1 / y := by
      rw [neg_div, neg_le_neg_iff, div_le_one hy0]; exact hy1
    have hb := rpow_one_add_le_one_add_mul_self hs h1p.le (by linarith [hp.1])
    have hnn : 0 ≤ 1 + -1 / y := by linarith
    have hFp : (F : ℝ) ^ (1 - p) = y ^ (1 - p) * (1 + -1 / y) ^ (1 - p) := by
      rw [hF, Real.mul_rpow hy0.le hnn]
    set u : ℝ := y ^ (-p) with hu
    have hyu : y ^ (1 - p) = u * y := by
      rw [hu, show (1 : ℝ) - p = -p + 1 by ring, Real.rpow_add hy0, Real.rpow_one]
    have hu0 : 0 < u := by positivity
    have key : (F : ℝ) ^ (1 - p) + (1 - p) * u ≤ u * y := by
      rw [hFp, hyu]
      have : u * y * (1 + -1 / y) ^ (1 - p) ≤ u * y * (1 + (1 - p) * (-1 / y)) :=
        mul_le_mul_of_nonneg_left hb (by positivity)
      have e : u * y * (1 + (1 - p) * (-1 / y)) = u * y - (1 - p) * u := by
        field_simp; ring
      linarith
    calc ∑ k ∈ Finset.Icc 1 F, (k : ℝ) ^ (-p) + y ^ (-p)
        ≤ (F : ℝ) ^ (1 - p) / (1 - p) + u := by linarith
      _ ≤ u * y / (1 - p) := by
          rw [div_add' _ _ _ h1p.ne', div_le_div_iff_of_pos_right h1p]; linarith
      _ = y ^ (1 - p) / (1 - p) := by rw [hyu]

theorem solution (p γ δ : ℝ) (hp : p ∈ Set.Ioo (0 : ℝ) 1) (hγ₁ : 3 / 4 < γ) (hγ₂ : γ < 1)
    (hδ₁ : p + (1 - p) * γ < δ) (hδ₂ : δ < 1) :
    Tendsto (fun T : ℕ => ∑ k ∈ Finset.Icc 1 ⌊(T : ℝ) ^ γ⌋₊,
      (wLaw p k T).real {w | (T : ℝ) ^ δ < (w : ℝ)}) atTop (𝓝 0) := by
  have h1p : 0 < 1 - p := by linarith [hp.2]
  set e : ℝ := δ - p - γ * (1 - p) with he
  have he0 : 0 < e := by rw [he]; nlinarith
  set C : ℝ := 2 / (1 - p) with hC
  have hlim : Tendsto (fun T : ℕ => C * (T : ℝ) ^ (-e)) atTop (𝓝 0) := by
    have := ((tendsto_rpow_neg_atTop he0).comp tendsto_natCast_atTop_atTop).const_mul C
    simpa using this
  apply squeeze_zero' (Eventually.of_forall fun T => Finset.sum_nonneg fun k _ =>
    measureReal_nonneg) _ hlim
  filter_upwards [eventually_ge_atTop 1] with T hT
  have hT1 : (1 : ℝ) ≤ T := by exact_mod_cast hT
  have hT0 : (0 : ℝ) < T := by linarith
  set F := ⌊(T : ℝ) ^ γ⌋₊ with hFdef
  have hFT : (F : ℝ) ≤ (T : ℝ) ^ γ := Nat.floor_le (by positivity)
  have hTγT : (T : ℝ) ^ γ ≤ T := by
    calc (T : ℝ) ^ γ ≤ (T : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hT1 hγ₂.le
      _ = T := Real.rpow_one _
  have hFT' : F ≤ T := by exact_mod_cast hFT.trans hTγT
  -- per-term bound
  have hterm : ∀ k ∈ Finset.Icc 1 F, (wLaw p k T).real {w | (T : ℝ) ^ δ < (w : ℝ)} ≤
      2 * (T : ℝ) ^ (p - δ) * (k : ℝ) ^ (-p) := by
    intro k hk
    obtain ⟨hk1, hkF⟩ := Finset.mem_Icc.mp hk
    have hkT : k ≤ T := hkF.trans hFT'
    have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk1
    have hk0 : (0 : ℝ) < k := by linarith
    simp only [wLaw, if_pos hkT]
    have hI : ∫⁻ w, ENNReal.ofReal ((w : ℕ) : ℝ) ∂(wChain p k (T - k)) =
        ENNReal.ofReal (∏ j ∈ Finset.range (T - k), (1 + p / ((k : ℝ) + j))) := by
      simp_rw [ENNReal.ofReal_natCast]; exact LDE_mean p hp k hk1 (T - k)
    have hM := LDE_markov (wChain p k (T - k)) (fun w => (w : ℝ)) _
      (Finset.prod_nonneg fun j _ => by have := hp.1.le; positivity) hI ((T : ℝ) ^ δ)
      (by positivity) {w | (T : ℝ) ^ δ < (w : ℝ)} (fun w hw => le_of_lt hw)
    refine hM.trans ?_
    have hprod := LDE_prod_le p hp.1.le k hk1 (T - k)
    have hkm : (k : ℝ) + ((T - k : ℕ) : ℝ) = T := by
      rw [Nat.cast_sub hkT]; ring
    rw [hkm] at hprod
    have hTδ : 0 < (T : ℝ) ^ δ := by positivity
    calc (∏ j ∈ Finset.range (T - k), (1 + p / ((k : ℝ) + j))) / (T : ℝ) ^ δ
        ≤ ((1 + p) * ((T : ℝ) / k) ^ p) / (T : ℝ) ^ δ :=
          div_le_div_of_nonneg_right hprod hTδ.le
      _ ≤ (2 * ((T : ℝ) / k) ^ p) / (T : ℝ) ^ δ := by
          apply div_le_div_of_nonneg_right _ hTδ.le
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          linarith [hp.2]
      _ = 2 * (T : ℝ) ^ (p - δ) * (k : ℝ) ^ (-p) := by
          rw [Real.div_rpow hT0.le hk0.le, Real.rpow_sub hT0, Real.rpow_neg hk0.le]
          field_simp
  calc ∑ k ∈ Finset.Icc 1 F, (wLaw p k T).real {w | (T : ℝ) ^ δ < (w : ℝ)}
      ≤ ∑ k ∈ Finset.Icc 1 F, 2 * (T : ℝ) ^ (p - δ) * (k : ℝ) ^ (-p) :=
        Finset.sum_le_sum hterm
    _ = 2 * (T : ℝ) ^ (p - δ) * ∑ k ∈ Finset.Icc 1 F, (k : ℝ) ^ (-p) := by
        rw [Finset.mul_sum]
    _ ≤ 2 * (T : ℝ) ^ (p - δ) * ((F : ℝ) ^ (1 - p) / (1 - p)) :=
        mul_le_mul_of_nonneg_left (LDE_sum_rpow p hp F) (by positivity)
    _ ≤ 2 * (T : ℝ) ^ (p - δ) * (((T : ℝ) ^ γ) ^ (1 - p) / (1 - p)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply div_le_div_of_nonneg_right _ h1p.le
        exact Real.rpow_le_rpow (by positivity) hFT h1p.le
    _ = C * (T : ℝ) ^ (-e) := by
        rw [← Real.rpow_mul hT0.le, hC, he]
        have : -(δ - p - γ * (1 - p)) = (p - δ) + γ * (1 - p) := by ring
        rw [this, Real.rpow_add hT0]
        field_simp
