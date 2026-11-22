-- Prove2me | solution 1 for LearnCollude.cesaro_tendstoInMeasure
-- status  : ACCEPTED   (prove)
-- author  : @ducloc
-- created : 2026-11-22T14:45:37.546565+00:00
-- url     : https://prove2.me/submissions/44a7e283-3e94-4b60-a03c-7e2cdca5ef84

import Mathlib

open Filter MeasureTheory
open scoped Topology ENNReal

theorem solution {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ) (B : ℝ) (hX : ∀ n, Measurable (X n))
    (hB : ∀ n x, |X n x| ≤ B) (hlim : TendstoInMeasure μ X atTop (fun _ => 0)) :
    TendstoInMeasure μ (fun (n : ℕ) x => (n : ℝ)⁻¹ * ∑ k ∈ Finset.Icc 1 n, X k x) atTop
      (fun _ => 0) := by
  -- replace `B` by a nonnegative bound
  let B' : ℝ := max B 0
  have hB'0 : 0 ≤ B' := le_max_right B 0
  have hB' : ∀ n x, |X n x| ≤ B' := fun n x => (hB n x).trans (le_max_left B 0)
  have h1B' : 0 < 1 + B' := by linarith
  -- rewrite the sum over `Icc 1 n` as a sum over `range n`
  have hshift : ∀ (n : ℕ) (x : Ω),
      ∑ k ∈ Finset.Icc 1 n, X k x = ∑ k ∈ Finset.range n, X (k + 1) x := by
    intro n x
    have hIcc : (Finset.Icc 1 n : Finset ℕ) = Finset.Ico 1 (n + 1) := by
      ext k
      simp only [Finset.mem_Icc, Finset.mem_Ico]
      omega
    rw [hIcc]
    have h := Finset.sum_Ico_eq_sum_range (f := fun k => X k x) 1 (n + 1)
    simpa [Nat.add_comm] using h
  simp only [hshift]
  rw [tendstoInMeasure_iff_measureReal_norm]
  intro ε hε
  rw [Metric.tendsto_nhds]
  intro η hη
  have hη2 : 0 < η / 2 := by linarith
  -- the truncation level
  set δ : ℝ := ε * (η / 2) / (2 * (1 + B')) with hδdef
  have hδ : 0 < δ := by
    rw [hδdef]
    exact div_pos (mul_pos hε hη2) (by linarith)
  have hC : (1 + B') * δ = ε * (η / 2) / 2 := by
    rw [hδdef]
    field_simp
  -- convergence in measure gives a threshold `K`
  have hlim_real : Tendsto (fun k : ℕ => μ.real {x : Ω | δ ≤ |X k x|}) atTop (𝓝 0) := by
    have h := (tendstoInMeasure_iff_measureReal_norm.mp hlim) δ hδ
    simpa [Real.norm_eq_abs, sub_zero] using h
  have hev : ∀ᶠ k : ℕ in atTop, μ.real {x : Ω | δ ≤ |X k x|} < δ := by
    have h := (Metric.tendsto_nhds.mp hlim_real) δ hδ
    filter_upwards [h] with k hk
    rwa [Real.dist_eq, sub_zero,
      abs_of_nonneg (measureReal_nonneg (μ := μ) (s := {x : Ω | δ ≤ |X k x|}))] at hk
  obtain ⟨K, hK⟩ := Filter.eventually_atTop.mp hev
  -- crude bound for every `X k`
  have hIall : ∀ k : ℕ, ∫⁻ x, ENNReal.ofReal |X k x| ∂μ ≤ ENNReal.ofReal B' := by
    intro k
    calc ∫⁻ x, ENNReal.ofReal |X k x| ∂μ
        ≤ ∫⁻ _x, ENNReal.ofReal B' ∂μ :=
          lintegral_mono fun x => ENNReal.ofReal_le_ofReal (hB' k x)
      _ = ENNReal.ofReal B' := by
          rw [lintegral_const]
          simp
  -- small bound for `X k`, `k ≥ K`
  have hIsmall : ∀ k : ℕ, K ≤ k →
      ∫⁻ x, ENNReal.ofReal |X k x| ∂μ ≤ ENNReal.ofReal ((1 + B') * δ) := by
    intro k hk
    have hmeas_ind : MeasurableSet {x : Ω | δ ≤ |X k x|} :=
      measurableSet_le measurable_const (continuous_abs.measurable.comp (hX k))
    have hpoint : ∀ x : Ω, ENNReal.ofReal |X k x| ≤
        ENNReal.ofReal δ + ENNReal.ofReal B' *
          ({x : Ω | δ ≤ |X k x|}.indicator (1 : Ω → ℝ≥0∞) x) := by
      intro x
      by_cases hx : δ ≤ |X k x|
      · rw [Set.indicator_of_mem (s := {x : Ω | δ ≤ |X k x|}) hx]
        simp only [Pi.one_apply, mul_one]
        exact (ENNReal.ofReal_le_ofReal (hB' k x)).trans
          (le_add_of_nonneg_left zero_le)
      · rw [Set.indicator_of_notMem (s := {x : Ω | δ ≤ |X k x|}) hx]
        simp only [mul_zero, add_zero]
        exact ENNReal.ofReal_le_ofReal (le_of_lt (lt_of_not_ge hx))
    have hs : μ {x : Ω | δ ≤ |X k x|} ≤ ENNReal.ofReal δ := by
      rw [← ENNReal.toReal_le_toReal (measure_ne_top μ _) ENNReal.ofReal_ne_top,
        ← measureReal_def, ENNReal.toReal_ofReal hδ.le]
      exact le_of_lt (hK k hk)
    calc ∫⁻ x, ENNReal.ofReal |X k x| ∂μ
        ≤ ∫⁻ x, (ENNReal.ofReal δ + ENNReal.ofReal B' *
            ({x : Ω | δ ≤ |X k x|}.indicator (1 : Ω → ℝ≥0∞) x)) ∂μ :=
          lintegral_mono hpoint
      _ = ENNReal.ofReal δ * μ Set.univ +
            ENNReal.ofReal B' * μ {x : Ω | δ ≤ |X k x|} := by
          rw [lintegral_add_left measurable_const, lintegral_const]
          congr 1
          have hconst : (fun a : Ω => ENNReal.ofReal B' *
              {x : Ω | δ ≤ |X k x|}.indicator (1 : Ω → ℝ≥0∞) a)
              = fun a : Ω => {x : Ω | δ ≤ |X k x|}.indicator
                  (fun _ => ENNReal.ofReal B') a := by
            funext a
            by_cases ha : a ∈ {x : Ω | δ ≤ |X k x|}
            · rw [Set.indicator_of_mem ha, Set.indicator_of_mem ha, Pi.one_apply,
                mul_one]
            · rw [Set.indicator_of_notMem ha, Set.indicator_of_notMem ha, mul_zero]
          rw [hconst, lintegral_indicator_const hmeas_ind (ENNReal.ofReal B')]
      _ = ENNReal.ofReal δ + ENNReal.ofReal B' * μ {x : Ω | δ ≤ |X k x|} := by
          simp
      _ ≤ ENNReal.ofReal δ + ENNReal.ofReal B' * ENNReal.ofReal δ := by
          gcongr
      _ = ENNReal.ofReal ((1 + B') * δ) := by
          rw [← ENNReal.ofReal_mul hB'0,
            ← ENNReal.ofReal_add hδ.le (mul_nonneg hB'0 hδ.le)]
          congr 1
          ring
  -- choose `N`
  obtain ⟨N₁, hN₁⟩ := exists_nat_gt (K : ℝ)
  obtain ⟨N₂, hN₂⟩ := exists_nat_gt (2 * ((K : ℝ) * B') / (ε * (η / 2)))
  let N : ℕ := max N₁ (max N₂ 1)
  have hNK : K ≤ N := by
    have h : (K : ℝ) ≤ (N : ℝ) := by
      have h1 : (K : ℝ) < (N₁ : ℝ) := hN₁
      have h2 : (N₁ : ℝ) ≤ (N : ℝ) := by
        exact_mod_cast le_max_left N₁ (max N₂ 1)
      linarith
    exact_mod_cast h
  have hN1 : 1 ≤ N := le_trans (le_max_right N₂ 1) (le_max_right N₁ (max N₂ 1))
  have hNB : 2 * ((K : ℝ) * B') / (ε * (η / 2)) < (N : ℝ) := by
    have h2 : (N₂ : ℝ) ≤ (N : ℝ) := by
      exact_mod_cast le_trans (le_max_left N₂ 1) (le_max_right N₁ (max N₂ 1))
    linarith
  -- main eventual bound
  have hmain : ∀ᶠ n : ℕ in atTop,
      μ {x : Ω | ε ≤ |(n : ℝ)⁻¹ * ∑ k ∈ Finset.range n, X (k + 1) x|} ≤
        ENNReal.ofReal (η / 2) := by
    filter_upwards [Filter.eventually_ge_atTop N] with n hn
    have hnK : K ≤ n := le_trans hNK hn
    have hn1 : 1 ≤ n := le_trans hN1 hn
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1
    have hεθ : 0 < ε * (η / 2) := mul_pos hε hη2
    -- factor out `n⁻¹`
    have hstep : ∫⁻ x, ENNReal.ofReal |(n : ℝ)⁻¹ * ∑ k ∈ Finset.range n, X (k + 1) x| ∂μ
        ≤ ENNReal.ofReal ((n : ℝ)⁻¹) *
            ∑ k ∈ Finset.range n, ∫⁻ x, ENNReal.ofReal |X (k + 1) x| ∂μ := by
      have hsummeas : Measurable (fun x : Ω =>
          ∑ k ∈ Finset.range n, ENNReal.ofReal |X (k + 1) x|) :=
        Finset.measurable_fun_sum _ fun k _ =>
          continuous_abs.measurable.comp (hX (k + 1)) |> Measurable.ennreal_ofReal
      calc
        ∫⁻ x, ENNReal.ofReal |(n : ℝ)⁻¹ * ∑ k ∈ Finset.range n, X (k + 1) x| ∂μ
            ≤ ∫⁻ x, ENNReal.ofReal ((n : ℝ)⁻¹) *
                ∑ k ∈ Finset.range n, ENNReal.ofReal |X (k + 1) x| ∂μ := by
              refine lintegral_mono fun x => ?_
              have hx1 : |(n : ℝ)⁻¹ * ∑ k ∈ Finset.range n, X (k + 1) x|
                  = (n : ℝ)⁻¹ * |∑ k ∈ Finset.range n, X (k + 1) x| := by
                rw [abs_mul, abs_of_nonneg (inv_nonneg.mpr (Nat.cast_nonneg n))]
              rw [hx1]
              calc ENNReal.ofReal ((n : ℝ)⁻¹ * |∑ k ∈ Finset.range n, X (k + 1) x|)
                  ≤ ENNReal.ofReal ((n : ℝ)⁻¹ *
                      ∑ k ∈ Finset.range n, |X (k + 1) x|) := by
                    refine ENNReal.ofReal_le_ofReal ?_
                    exact mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _)
                      (inv_nonneg.mpr (Nat.cast_nonneg n))
                _ = ENNReal.ofReal ((n : ℝ)⁻¹) *
                      ENNReal.ofReal (∑ k ∈ Finset.range n, |X (k + 1) x|) :=
                    ENNReal.ofReal_mul (inv_nonneg.mpr (Nat.cast_nonneg n))
                _ = ENNReal.ofReal ((n : ℝ)⁻¹) *
                      ∑ k ∈ Finset.range n, ENNReal.ofReal |X (k + 1) x| := by
                    rw [ENNReal.ofReal_sum_of_nonneg (fun k _ => abs_nonneg _)]
        _ = ENNReal.ofReal ((n : ℝ)⁻¹) *
              ∫⁻ x, ∑ k ∈ Finset.range n, ENNReal.ofReal |X (k + 1) x| ∂μ :=
            lintegral_const_mul _ hsummeas
        _ = ENNReal.ofReal ((n : ℝ)⁻¹) *
              ∑ k ∈ Finset.range n, ∫⁻ x, ENNReal.ofReal |X (k + 1) x| ∂μ := by
            congr 1
            exact lintegral_finsetSum (Finset.range n) fun k _ =>
              continuous_abs.measurable.comp (hX (k + 1)) |> Measurable.ennreal_ofReal
    -- split the sum at `K`
    have hsum : ∑ k ∈ Finset.range n, ∫⁻ x, ENNReal.ofReal |X (k + 1) x| ∂μ
        ≤ ENNReal.ofReal ((K : ℝ) * B') +
            ENNReal.ofReal (((n - K : ℕ) : ℝ) * ((1 + B') * δ)) := by
      conv_lhs => rw [← Nat.add_sub_of_le hnK]
      rw [Finset.sum_range_add]
      refine add_le_add ?_ ?_
      · calc ∑ k ∈ Finset.range K, ∫⁻ x, ENNReal.ofReal |X (k + 1) x| ∂μ
            ≤ ∑ k ∈ Finset.range K, ENNReal.ofReal B' :=
              Finset.sum_le_sum fun k _ => hIall (k + 1)
          _ = (K : ℝ≥0∞) * ENNReal.ofReal B' := by
              simp [Finset.sum_const, nsmul_eq_mul]
          _ = ENNReal.ofReal ((K : ℝ) * B') := by
              rw [← ENNReal.ofReal_natCast K, ← ENNReal.ofReal_mul (Nat.cast_nonneg K)]
      · calc ∑ k ∈ Finset.range (n - K), ∫⁻ x, ENNReal.ofReal |X (K + k + 1) x| ∂μ
            ≤ ∑ k ∈ Finset.range (n - K), ENNReal.ofReal ((1 + B') * δ) :=
              Finset.sum_le_sum fun k _ => hIsmall (K + k + 1) (by omega)
          _ = ((n - K : ℕ) : ℝ≥0∞) * ENNReal.ofReal ((1 + B') * δ) := by
              simp [Finset.sum_const, nsmul_eq_mul]
          _ = ENNReal.ofReal (((n - K : ℕ) : ℝ) * ((1 + B') * δ)) := by
              rw [← ENNReal.ofReal_natCast (n - K),
                ← ENNReal.ofReal_mul (Nat.cast_nonneg (n - K))]
    -- bound the integral by `ofReal (ε * (η/2))`
    have hJ : ∫⁻ x, ENNReal.ofReal |(n : ℝ)⁻¹ * ∑ k ∈ Finset.range n, X (k + 1) x| ∂μ
        ≤ ENNReal.ofReal (ε * (η / 2)) := by
      have hKB0 : 0 ≤ (K : ℝ) * B' := mul_nonneg (Nat.cast_nonneg K) hB'0
      have hrest0 : 0 ≤ ((n - K : ℕ) : ℝ) * ((1 + B') * δ) :=
        mul_nonneg (Nat.cast_nonneg _) (mul_nonneg h1B'.le hδ.le)
      have hinv0 : 0 ≤ (n : ℝ)⁻¹ := inv_nonneg.mpr (Nat.cast_nonneg n)
      have hreal : (n : ℝ)⁻¹ *
          ((K : ℝ) * B' + ((n - K : ℕ) : ℝ) * ((1 + B') * δ)) ≤ ε * (η / 2) := by
        rw [← div_eq_inv_mul, div_le_iff₀ hnpos]
        have hNBlt : 2 * ((K : ℝ) * B') < (n : ℝ) * (ε * (η / 2)) := by
          have hNle : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
          have hlt : 2 * ((K : ℝ) * B') / (ε * (η / 2)) < (n : ℝ) :=
            lt_of_lt_of_le hNB hNle
          rwa [div_lt_iff₀ hεθ] at hlt
        have hKB : (K : ℝ) * B' ≤ (n : ℝ) * (ε * (η / 2)) / 2 := by linarith
        have hsub : ((n - K : ℕ) : ℝ) ≤ (n : ℝ) := by
          exact_mod_cast Nat.sub_le n K
        have hC0 : 0 ≤ (1 + B') * δ := mul_nonneg h1B'.le hδ.le
        have hrest : ((n - K : ℕ) : ℝ) * ((1 + B') * δ) ≤
            (n : ℝ) * (ε * (η / 2)) / 2 := by
          calc ((n - K : ℕ) : ℝ) * ((1 + B') * δ)
              ≤ (n : ℝ) * ((1 + B') * δ) := mul_le_mul_of_nonneg_right hsub hC0
            _ = (n : ℝ) * (ε * (η / 2) / 2) := by rw [hC]
            _ = (n : ℝ) * (ε * (η / 2)) / 2 := by ring
        linarith
      calc ∫⁻ x, ENNReal.ofReal |(n : ℝ)⁻¹ * ∑ k ∈ Finset.range n, X (k + 1) x| ∂μ
          ≤ ENNReal.ofReal ((n : ℝ)⁻¹) *
              ∑ k ∈ Finset.range n, ∫⁻ x, ENNReal.ofReal |X (k + 1) x| ∂μ := hstep
        _ ≤ ENNReal.ofReal ((n : ℝ)⁻¹) *
              (ENNReal.ofReal ((K : ℝ) * B') +
                ENNReal.ofReal (((n - K : ℕ) : ℝ) * ((1 + B') * δ))) := by
            gcongr
        _ = ENNReal.ofReal ((n : ℝ)⁻¹ *
              ((K : ℝ) * B' + ((n - K : ℕ) : ℝ) * ((1 + B') * δ))) := by
            conv_lhs => rw [← ENNReal.ofReal_add hKB0 hrest0,
              ← ENNReal.ofReal_mul hinv0]
        _ ≤ ENNReal.ofReal (ε * (η / 2)) := ENNReal.ofReal_le_ofReal hreal
    -- Markov's inequality
    have hSmeas : Measurable (fun x : Ω =>
        (n : ℝ)⁻¹ * ∑ k ∈ Finset.range n, X (k + 1) x) :=
      measurable_const.mul (Finset.measurable_fun_sum _ fun k _ => hX (k + 1))
    have habsmeas : Measurable (fun x : Ω =>
        ENNReal.ofReal |(n : ℝ)⁻¹ * ∑ k ∈ Finset.range n, X (k + 1) x|) :=
      Measurable.ennreal_ofReal (continuous_abs.measurable.comp hSmeas)
    have hMarkov := mul_meas_ge_le_lintegral
      (μ := μ)
      (f := fun x : Ω => ENNReal.ofReal |(n : ℝ)⁻¹ * ∑ k ∈ Finset.range n, X (k + 1) x|)
      habsmeas (ENNReal.ofReal ε)
    have hset_eq : {x : Ω | ENNReal.ofReal ε ≤
          ENNReal.ofReal |(n : ℝ)⁻¹ * ∑ k ∈ Finset.range n, X (k + 1) x|}
        = {x : Ω | ε ≤ |(n : ℝ)⁻¹ * ∑ k ∈ Finset.range n, X (k + 1) x|} := by
      ext x
      exact ENNReal.ofReal_le_ofReal_iff (abs_nonneg _)
    have hmul : ENNReal.ofReal ε *
        μ {x : Ω | ε ≤ |(n : ℝ)⁻¹ * ∑ k ∈ Finset.range n, X (k + 1) x|} ≤
        ENNReal.ofReal ε * ENNReal.ofReal (η / 2) := by
      calc ENNReal.ofReal ε *
            μ {x : Ω | ε ≤ |(n : ℝ)⁻¹ * ∑ k ∈ Finset.range n, X (k + 1) x|}
          = ENNReal.ofReal ε * μ {x : Ω | ENNReal.ofReal ε ≤
              ENNReal.ofReal |(n : ℝ)⁻¹ * ∑ k ∈ Finset.range n, X (k + 1) x|} := by
            rw [hset_eq]
        _ ≤ ∫⁻ x, ENNReal.ofReal |(n : ℝ)⁻¹ * ∑ k ∈ Finset.range n, X (k + 1) x| ∂μ :=
            hMarkov
        _ ≤ ENNReal.ofReal (ε * (η / 2)) := hJ
        _ = ENNReal.ofReal ε * ENNReal.ofReal (η / 2) := ENNReal.ofReal_mul hε.le
    exact (ENNReal.mul_le_mul_iff_right
      (ENNReal.ofReal_pos.mpr hε).ne' ENNReal.ofReal_ne_top).1 hmul
  -- final conversion to the distance formulation
  filter_upwards [hmain] with n hn
  have hset2 : {x : Ω | ε ≤ ‖(n : ℝ)⁻¹ * ∑ k ∈ Finset.range n, X (k + 1) x - 0‖}
      = {x : Ω | ε ≤ |(n : ℝ)⁻¹ * ∑ k ∈ Finset.range n, X (k + 1) x|} := by
    ext x
    simp
  rw [hset2]
  have hreal : μ.real {x : Ω | ε ≤ |(n : ℝ)⁻¹ * ∑ k ∈ Finset.range n, X (k + 1) x|} ≤
      η / 2 := by
    rw [measureReal_def]
    calc (μ {x : Ω | ε ≤ |(n : ℝ)⁻¹ * ∑ k ∈ Finset.range n, X (k + 1) x|}).toReal
        ≤ (ENNReal.ofReal (η / 2)).toReal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hn
      _ = η / 2 := ENNReal.toReal_ofReal hη2.le
  rw [Real.dist_eq, sub_zero,
    abs_of_nonneg (measureReal_nonneg (μ := μ)
      (s := {x : Ω | ε ≤ |(n : ℝ)⁻¹ * ∑ k ∈ Finset.range n, X (k + 1) x|}))]
  linarith
