-- Prove2me | solution 1 for LostSalesExpGap.ConstOrder.lemma_5
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T07:21:44.300687+00:00
-- url     : https://prove2.me/submissions/04b7c94e-2389-48ae-a853-6b63eb86c1e5

import Mathlib
import Definitions.Def_LostSalesExpGap_ConstOrder_ConstantOrder
import Theorems.Thm_LostSalesExpGap_ConstOrder_eq_3
import Theorems.Thm_LostSalesExpGap_ConstOrder_lemma_3
import Theorems.Thm_LostSalesExpGap_ConstOrder_best_constant_exists

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace LSExpGapL5

open CappedBaseStock Filter Topology

/-- Chernoff bound at an arbitrary level `x`: `P(S_N ≤ N x) ≤ ψ(θ)^N`. -/
lemma chernoff_level (P : DemandLaw) (x θ : ℝ) (hθ : 0 ≤ θ) (N : ℕ) :
    (demandPathLaw P).real {d | ∑ i ∈ Finset.range N, (d i : ℝ) ≤ (N : ℝ) * x} ≤
      (Real.exp (θ * x) * ∫ y : ℝ≥0, Real.exp (-θ * (y : ℝ)) ∂P.law) ^ N := by
  set μ := demandPathLaw P with hμ
  let X : ℕ → DemandPath → ℝ := fun i d => (d i : ℝ)
  have hXm : ∀ i, Measurable (X i) := fun i => by fun_prop
  have hind : iIndepFun X μ :=
    iIndepFun_infinitePi (P := fun _ : ℕ => P.law) (X := fun _ (x : ℝ≥0) => (x : ℝ))
      (fun _ => by fun_prop)
  have hmgf1 : ∀ i (t : ℝ), mgf (X i) μ t = ∫ y : ℝ≥0, Real.exp (t * (y : ℝ)) ∂P.law := by
    intro i t
    simp only [mgf, X]
    have hmap : μ.map (fun d : DemandPath => d i) = P.law := by
      simp only [hμ, demandPathLaw]
      exact Measure.infinitePi_map_eval _ i
    rw [← hmap, integral_map (measurable_pi_apply i).aemeasurable]
    exact (Measurable.aestronglyMeasurable (by fun_prop))
  set S : DemandPath → ℝ := ∑ i ∈ Finset.range N, X i with hS
  have hSapp : ∀ d, S d = ∑ i ∈ Finset.range N, (d i : ℝ) := by
    intro d; simp [hS, X, Finset.sum_apply]
  have hset : {d : DemandPath | ∑ i ∈ Finset.range N, (d i : ℝ) ≤ (N : ℝ) * x}
      = {d | S d ≤ (N : ℝ) * x} := by
    ext d; simp [hSapp]
  have hS0 : ∀ d, 0 ≤ S d := fun d => by rw [hSapp]; positivity
  have hint : Integrable (fun d => Real.exp (-θ * S d)) μ := by
    refine Integrable.of_bound (C := 1) ?_ (ae_of_all _ fun d => ?_)
    · have : Measurable S := by
        rw [show S = fun d => ∑ i ∈ Finset.range N, (d i : ℝ) from funext hSapp]; fun_prop
      exact (Measurable.aestronglyMeasurable (by fun_prop))
    · rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.exp_le_one_iff]
      nlinarith [hS0 d]
  have h := measure_le_le_exp_mul_mgf (μ := μ) (X := S) ((N : ℝ) * x) (neg_nonpos.mpr hθ) hint
  have hsum : mgf S μ (-θ) = (∫ y : ℝ≥0, Real.exp (-θ * (y : ℝ)) ∂P.law) ^ N := by
    rw [hS, hind.mgf_sum hXm]
    simp_rw [hmgf1]
    rw [Finset.prod_const, Finset.card_range]
  rw [hsum] at h
  rw [hset]
  refine h.trans (le_of_eq ?_)
  rw [mul_pow, ← Real.exp_nat_mul]
  congr 2; ring

/-- For a level `x ∈ [0, E[D])` the exponential moment `ψ(θ) = e^{θx}E[e^{-θD}]` is `< 1` for
some `θ ≥ 0`. -/
lemma exists_psi_lt_one (P : DemandLaw) (x : ℝ) (hx0 : 0 ≤ x) (hxm : x < mean P) :
    ∃ θ : ℝ, 0 ≤ θ ∧ Real.exp (θ * x) * ∫ y : ℝ≥0, Real.exp (-θ * (y : ℝ)) ∂P.law < 1 := by
  have htrunc : ∃ M : ℝ, 0 < M ∧ x < ∫ d : ℝ≥0, min (d : ℝ) M ∂P.law := by
    have hlim : Tendsto (fun n : ℕ => ∫ d : ℝ≥0, min (d : ℝ) ((n : ℝ) + 1) ∂P.law) atTop
        (𝓝 (∫ d : ℝ≥0, (d : ℝ) ∂P.law)) := by
      refine tendsto_integral_of_dominated_convergence (fun d : ℝ≥0 => (d : ℝ))
        (fun n => (Measurable.aestronglyMeasurable (by fun_prop))) P.finiteMean
        (fun n => ae_of_all _ fun d => ?_) (ae_of_all _ fun d => ?_)
      · rw [Real.norm_eq_abs, abs_of_nonneg (le_min (NNReal.coe_nonneg d) (by positivity))]
        exact min_le_left _ _
      · apply tendsto_const_nhds.congr'
        filter_upwards [eventually_ge_atTop (⌈(d : ℝ)⌉₊)] with n hn
        have : (d : ℝ) ≤ (n : ℝ) + 1 := by
          have := Nat.le_ceil (d : ℝ)
          have : (⌈(d : ℝ)⌉₊ : ℝ) ≤ n := by exact_mod_cast hn
          linarith
        exact (min_eq_left this).symm
    have hev := hlim.eventually (lt_mem_nhds (show x < ∫ d : ℝ≥0, (d : ℝ) ∂P.law from hxm))
    obtain ⟨n, hn⟩ := hev.exists
    exact ⟨(n : ℝ) + 1, by positivity, hn⟩
  obtain ⟨M, hM, hb⟩ := htrunc
  set b := ∫ d : ℝ≥0, min (d : ℝ) M ∂P.law with hbdef
  have hbpos : 0 < b := lt_of_le_of_lt hx0 hb
  set θ := (b - x) / (2 * M * b) with hθ
  have hθpos : 0 < θ := by
    apply div_pos (by linarith); positivity
  have hθM : θ * M ≤ 1 := by
    rw [hθ, div_mul_eq_mul_div, div_le_one (by positivity)]
    nlinarith
  have hpt : ∀ d : ℝ≥0, Real.exp (-θ * (d : ℝ)) ≤
      1 - θ * min (d : ℝ) M + θ ^ 2 * M * min (d : ℝ) M := by
    intro d
    set y := θ * min (d : ℝ) M
    have hy0 : 0 ≤ y := mul_nonneg hθpos.le (le_min (NNReal.coe_nonneg d) hM.le)
    have hyM : y ≤ θ * M := mul_le_mul_of_nonneg_left (min_le_right _ _) hθpos.le
    have hy1 : y ≤ 1 := hyM.trans hθM
    have h1 : Real.exp (-θ * (d : ℝ)) ≤ Real.exp (-y) := by
      apply Real.exp_le_exp.mpr
      have := mul_le_mul_of_nonneg_left (min_le_left (d : ℝ) M) hθpos.le
      simp only [y]; linarith
    have h2 := Real.abs_exp_sub_one_sub_id_le (x := -y)
      (by rw [abs_neg, abs_of_nonneg hy0]; exact hy1)
    have h3 : Real.exp (-y) ≤ 1 - y + y ^ 2 := by
      have := (abs_le.mp h2).2; rw [neg_sq] at this; linarith
    have h4 : y ^ 2 ≤ θ ^ 2 * M * min (d : ℝ) M := by
      calc y ^ 2 = y * y := sq y
        _ ≤ (θ * M) * y := mul_le_mul_of_nonneg_right hyM hy0
        _ = θ ^ 2 * M * min (d : ℝ) M := by simp only [y]; ring
    linarith
  have hmin_int : Integrable (fun d : ℝ≥0 => min (d : ℝ) M) P.law := by
    refine Integrable.of_bound (C := M) (Measurable.aestronglyMeasurable (by fun_prop))
      (ae_of_all _ fun d => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (le_min (NNReal.coe_nonneg d) hM.le)]
    exact min_le_right _ _
  have hE : ∫ d : ℝ≥0, Real.exp (-θ * (d : ℝ)) ∂P.law ≤ 1 - θ * b + θ ^ 2 * M * b := by
    have hexp_int : Integrable (fun d : ℝ≥0 => Real.exp (-θ * (d : ℝ))) P.law := by
      refine Integrable.of_bound (C := 1) (Measurable.aestronglyMeasurable (by fun_prop))
        (ae_of_all _ fun d => ?_)
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.exp_le_one_iff]
      nlinarith [NNReal.coe_nonneg d]
    have hA : Integrable (fun d : ℝ≥0 => 1 - θ * min (d : ℝ) M) P.law :=
      (integrable_const 1).sub (hmin_int.const_mul θ)
    have hB : Integrable (fun d : ℝ≥0 => θ ^ 2 * M * min (d : ℝ) M) P.law :=
      hmin_int.const_mul _
    refine (integral_mono hexp_int (hA.add hB) hpt).trans (le_of_eq ?_)
    simp only [Pi.add_apply]
    rw [integral_add (f := fun d : ℝ≥0 => 1 - θ * min (d : ℝ) M)
      (g := fun d : ℝ≥0 => θ ^ 2 * M * min (d : ℝ) M) hA hB,
      integral_sub (f := fun _ : ℝ≥0 => (1 : ℝ)) (g := fun d : ℝ≥0 => θ * min (d : ℝ) M)
        (integrable_const 1) (hmin_int.const_mul θ), integral_const_mul,
      integral_const_mul]
    simp [hbdef]
  have hEr : ∫ d : ℝ≥0, Real.exp (-θ * (d : ℝ)) ∂P.law < 1 - θ * x := by
    have : θ * M * b < b - x := by
      rw [hθ]; field_simp; nlinarith
    nlinarith
  refine ⟨θ, hθpos.le, ?_⟩
  have hexp : Real.exp (θ * x) * (1 - θ * x) ≤ 1 := by
    have := Real.add_one_le_exp (-(θ * x))
    calc Real.exp (θ * x) * (1 - θ * x) ≤ Real.exp (θ * x) * Real.exp (-(θ * x)) :=
          mul_le_mul_of_nonneg_left (by linarith) (Real.exp_pos _).le
      _ = 1 := by rw [← Real.exp_add]; simp
  calc Real.exp (θ * x) * ∫ d : ℝ≥0, Real.exp (-θ * (d : ℝ)) ∂P.law
      < Real.exp (θ * x) * (1 - θ * x) := mul_lt_mul_of_pos_left hEr (Real.exp_pos _)
    _ ≤ 1 := hexp

/-- Summability of `n ↦ P(S_{n+1} ≤ (n+1) x)` for `x ∈ [0, E[D])`. -/
lemma summable_level (P : DemandLaw) (x : ℝ) (hx0 : 0 ≤ x) (hxm : x < mean P) :
    Summable (fun n : ℕ => (demandPathLaw P).real
      {d | ∑ i ∈ Finset.range (n + 1), (d i : ℝ) ≤ ((n : ℝ) + 1) * x}) := by
  obtain ⟨θ, hθ, hψ⟩ := exists_psi_lt_one P x hx0 hxm
  set ψ := Real.exp (θ * x) * ∫ y : ℝ≥0, Real.exp (-θ * (y : ℝ)) ∂P.law
  have hψ0 : 0 ≤ ψ :=
    mul_nonneg (Real.exp_pos _).le (integral_nonneg fun _ => (Real.exp_pos _).le)
  refine Summable.of_nonneg_of_le (fun n => measureReal_nonneg) (fun n => ?_)
    ((summable_geometric_of_lt_one hψ0 hψ).mul_right ψ)
  have h := chernoff_level P x θ hθ (n + 1)
  rw [← pow_succ]
  have e : {d : DemandPath | ∑ i ∈ Finset.range (n + 1), (d i : ℝ) ≤ ((n : ℝ) + 1) * x} =
      {d | ∑ i ∈ Finset.range (n + 1), (d i : ℝ) ≤ ((n + 1 : ℕ) : ℝ) * x} := by
    ext; push_cast; rfl
  rw [e]; exact h

end LSExpGapL5

open LostSalesExpGap.ConstOrder LSExpGapL5 CappedBaseStock Filter Topology in
theorem solution (P : CappedBaseStock.DemandLaw) (c : CappedBaseStock.Parameters)
    (hP : LostSalesConstantOrder.LargeLeadTime.NonDeterministic P) :
    ENNReal.ofReal (c.p / c.h) ≤
      ∑' n : ℕ, CappedBaseStock.demandPathLaw P
        {d | ∑ i ∈ Finset.range (n + 1), (d i : ℝ) ≤ ((n : ℝ) + 1) * rInf P c} := by
  obtain ⟨_, _, hrmem, hrlt⟩ := best_constant_exists P c hP
  obtain ⟨_, hK, _⟩ := lemma_3 P c hP
  have hh := c.holding_pos
  have hp := c.penalty_pos
  set μ := demandPathLaw P with hμ
  set r := rInf P c
  set m := mean P
  have hr0 : 0 ≤ r := hrmem.1.1
  have hm : 0 < m := P.positiveMean
  let B : ℝ → ℕ → Set DemandPath := fun x n =>
    {d | ∑ i ∈ Finset.range (n + 1), (d i : ℝ) ≤ ((n : ℝ) + 1) * x}
  have hBm : ∀ x n, MeasurableSet (B x n) := fun x n =>
    measurableSet_le (by fun_prop) (by fun_prop)
  let a : ℝ → ℕ → ℝ≥0∞ := fun x n => ENNReal.ofReal (1 / ((n : ℝ) + 1)) *
    ∫⁻ d, ENNReal.ofReal (((n : ℝ) + 1) * x - ∑ i ∈ Finset.range (n + 1), (d i : ℝ)) ∂μ
  -- Step A: increments of the Kingman terms
  have hA : ∀ ε, 0 ≤ ε → ∀ n, a (r + ε) n ≤ a r n + ENNReal.ofReal ε * μ (B (r + ε) n) := by
    intro ε hε n
    have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have hpt : ∀ d : DemandPath,
        ENNReal.ofReal (((n : ℝ) + 1) * (r + ε) - ∑ i ∈ Finset.range (n + 1), (d i : ℝ)) ≤
          ENNReal.ofReal (((n : ℝ) + 1) * r - ∑ i ∈ Finset.range (n + 1), (d i : ℝ)) +
          (B (r + ε) n).indicator (fun _ => ENNReal.ofReal (((n : ℝ) + 1) * ε)) d := by
      intro d
      by_cases hd : d ∈ B (r + ε) n
      · rw [Set.indicator_of_mem hd]
        refine le_trans (le_of_eq ?_) (ENNReal.ofReal_add_le)
        congr 1; ring
      · rw [Set.indicator_of_notMem hd, add_zero]
        have : ((n : ℝ) + 1) * (r + ε) - ∑ i ∈ Finset.range (n + 1), (d i : ℝ) ≤ 0 := by
          simp only [B, Set.mem_setOf_eq, not_le] at hd; linarith
        rw [ENNReal.ofReal_of_nonpos this]; simp
    have hint := lintegral_mono (μ := μ) hpt
    rw [lintegral_add_right _ ((measurable_const.indicator (hBm _ n))),
      lintegral_indicator_const (hBm _ n)] at hint
    calc a (r + ε) n ≤ ENNReal.ofReal (1 / ((n : ℝ) + 1)) *
          (∫⁻ d, ENNReal.ofReal (((n : ℝ) + 1) * r - ∑ i ∈ Finset.range (n + 1), (d i : ℝ)) ∂μ
            + ENNReal.ofReal (((n : ℝ) + 1) * ε) * μ (B (r + ε) n)) := by
          simp only [a]; gcongr
      _ = a r n + ENNReal.ofReal ε * μ (B (r + ε) n) := by
          rw [mul_add, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
          congr 3
          field_simp
  -- the Kingman series form of `E[I^x_∞]`
  have hKa : ∀ x, 0 ≤ x → x < m → EIinf P x = ∑' n, a x n := fun x hx0 hxm => hK x hx0 hxm
  -- Step B: finiteness of `h E[I^{r∞}_∞]`
  have hE0 : EIinf P 0 = 0 := by
    rw [hKa 0 le_rfl hm]
    apply ENNReal.tsum_eq_zero.mpr
    intro n
    have : (fun d : DemandPath => ENNReal.ofReal (((n : ℝ) + 1) * 0 -
        ∑ i ∈ Finset.range (n + 1), (d i : ℝ))) = fun _ => 0 := by
      funext d
      apply ENNReal.ofReal_of_nonpos
      have : 0 ≤ ∑ i ∈ Finset.range (n + 1), (d i : ℝ) := by positivity
      linarith
    show a 0 n = 0
    simp only [a]
    rw [this, lintegral_zero, mul_zero]
  have hfin0 : constCost P c 0 ≠ ⊤ := by
    rw [eq_3 P c 0 le_rfl hm, hE0, mul_zero, zero_add]
    exact ENNReal.ofReal_ne_top
  have hfinr : constCost P c r ≠ ⊤ :=
    ne_top_of_le_ne_top hfin0 (hrmem.2 0 ⟨le_rfl, hm.le⟩)
  rw [eq_3 P c r hr0 hrlt] at hfinr
  have hX0 : ENNReal.ofReal c.h * EIinf P r ≠ ⊤ := fun h => hfinr (by rw [h, top_add])
  -- Step C: for small ε > 0
  have hC : ∀ ε, 0 < ε → ε < m - r → ENNReal.ofReal (c.p / c.h) ≤ ∑' n, μ (B (r + ε) n) := by
    intro ε hε hεm
    have hle := hrmem.2 (r + ε) ⟨by linarith, by linarith⟩
    rw [eq_3 P c r hr0 hrlt, eq_3 P c (r + ε) (by linarith) (by linarith)] at hle
    set T := ∑' n, μ (B (r + ε) n)
    have hsum : EIinf P (r + ε) ≤ EIinf P r + ENNReal.ofReal ε * T := by
      rw [hKa (r + ε) (by linarith) (by linarith), hKa r hr0 hrlt, ← ENNReal.tsum_mul_left,
        ← ENNReal.tsum_add]
      exact ENNReal.tsum_le_tsum (hA ε hε.le)
    have h1 : ENNReal.ofReal c.h * EIinf P r + ENNReal.ofReal (c.p * (m - r)) ≤
        ENNReal.ofReal c.h * EIinf P r +
          (ENNReal.ofReal (c.h * ε) * T + ENNReal.ofReal (c.p * (m - (r + ε)))) := by
      refine hle.trans ?_
      calc ENNReal.ofReal c.h * EIinf P (r + ε) + ENNReal.ofReal (c.p * (m - (r + ε)))
          ≤ ENNReal.ofReal c.h * (EIinf P r + ENNReal.ofReal ε * T) +
              ENNReal.ofReal (c.p * (m - (r + ε))) := by gcongr
        _ = _ := by
          rw [mul_add, ENNReal.ofReal_mul hh.le, add_assoc, mul_assoc]
    have h2 := ENNReal.le_of_add_le_add_left hX0 h1
    have hsplit : ENNReal.ofReal (c.p * (m - r)) =
        ENNReal.ofReal (c.p * ε) + ENNReal.ofReal (c.p * (m - (r + ε))) := by
      rw [← ENNReal.ofReal_add (by positivity) (by nlinarith)]; congr 1; ring
    rw [hsplit] at h2
    have h3 := ENNReal.le_of_add_le_add_right ENNReal.ofReal_ne_top h2
    have hpe : ENNReal.ofReal (c.p * ε) = ENNReal.ofReal (c.h * ε) * ENNReal.ofReal (c.p / c.h) := by
      rw [← ENNReal.ofReal_mul (by positivity)]; congr 1; field_simp
    rw [hpe] at h3
    have hne : ENNReal.ofReal (c.h * ε) ≠ 0 := by
      rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]; positivity
    exact (ENNReal.mul_le_mul_iff_right hne ENNReal.ofReal_ne_top).mp h3
  -- Step D: let ε ↓ 0
  set δ0 := (m - r) / 2 with hδ0
  have hδ0pos : 0 < δ0 := by rw [hδ0]; linarith
  let ε : ℕ → ℝ := fun k => δ0 / ((k : ℝ) + 1)
  have hεpos : ∀ k, 0 < ε k := fun k => by positivity
  have hεle : ∀ k, ε k ≤ δ0 := fun k => by
    simp only [ε]; rw [div_le_iff₀ (by positivity)]; nlinarith [(Nat.cast_nonneg k : (0:ℝ) ≤ k)]
  have hεlt : ∀ k, ε k < m - r := fun k => by have := hεle k; linarith
  have hsumR : ∀ x, 0 ≤ x → x < m → (∑' n, μ (B x n)) = ENNReal.ofReal (∑' n, μ.real (B x n)) := by
    intro x hx0 hxm
    rw [ENNReal.ofReal_tsum_of_nonneg (fun n => measureReal_nonneg) (summable_level P x hx0 hxm)]
    congr 1; funext n
    exact (ofReal_measureReal (measure_ne_top _ _)).symm
  have hk : ∀ k, c.p / c.h ≤ ∑' n, μ.real (B (r + ε k) n) := by
    intro k
    have := hC (ε k) (hεpos k) (hεlt k)
    rw [hsumR (r + ε k) (by linarith [hεpos k]) (by linarith [hεlt k])] at this
    exact (ENNReal.ofReal_le_ofReal_iff (tsum_nonneg fun n => measureReal_nonneg)).mp this
  have hmono : ∀ n, Antitone (fun k => B (r + ε k) n) := by
    intro n k l hkl d hd
    simp only [B, Set.mem_setOf_eq] at hd ⊢
    have : ε l ≤ ε k := by
      simp only [ε]
      apply div_le_div_of_nonneg_left hδ0pos.le (by positivity)
      have : (k : ℝ) ≤ l := by exact_mod_cast hkl
      linarith
    have hn : (0 : ℝ) ≤ (n : ℝ) + 1 := by positivity
    nlinarith
  have hinter : ∀ n, (⋂ k, B (r + ε k) n) = B r n := by
    intro n
    ext d
    simp only [Set.mem_iInter, B, Set.mem_setOf_eq]
    constructor
    · intro hd
      by_contra hcon
      push_neg at hcon
      set g := ∑ i ∈ Finset.range (n + 1), (d i : ℝ) - ((n : ℝ) + 1) * r
      have hg : 0 < g := by simp only [g]; linarith
      obtain ⟨k, hk⟩ := exists_nat_gt (((n : ℝ) + 1) * δ0 / g)
      have h1 := hd k
      have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
      have hk1 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
      have : ((n : ℝ) + 1) * ε k < g := by
        simp only [ε]
        rw [mul_div_assoc', div_lt_iff₀ hk1]
        rw [div_lt_iff₀ hg] at hk
        nlinarith
      simp only [g] at this
      nlinarith
    · intro hd k
      have : (0 : ℝ) ≤ ((n : ℝ) + 1) * ε k := by have := hεpos k; positivity
      nlinarith
  have hlim : Tendsto (fun k => ∑' n, μ.real (B (r + ε k) n)) atTop
      (𝓝 (∑' n, μ.real (B r n))) := by
    refine tendsto_tsum_of_dominated_convergence
      (bound := fun n => μ.real (B (r + δ0) n))
      (summable_level P (r + δ0) (by linarith) (by rw [hδ0]; linarith)) (fun n => ?_)
      (Eventually.of_forall fun k n => ?_)
    · have h := tendsto_measure_iInter_atTop (μ := μ) (fun k => (hBm (r + ε k) n).nullMeasurableSet)
        (hmono n) ⟨0, measure_ne_top _ _⟩
      rw [hinter n] at h
      have h' := (ENNReal.tendsto_toReal (measure_ne_top μ (B r n))).comp h
      exact h'
    · rw [Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg]
      refine measureReal_mono ?_ (measure_ne_top _ _)
      intro d hd
      simp only [B, Set.mem_setOf_eq] at hd ⊢
      have hn : (0 : ℝ) ≤ (n : ℝ) + 1 := by positivity
      have := hεle k
      nlinarith
  have hfinal : c.p / c.h ≤ ∑' n, μ.real (B r n) := ge_of_tendsto' hlim hk
  have := hsumR r hr0 hrlt
  change ENNReal.ofReal (c.p / c.h) ≤ ∑' n, μ (B r n)
  rw [this]
  exact ENNReal.ofReal_le_ofReal hfinal
