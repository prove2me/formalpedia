-- Prove2me | solution 1 for MarkovChainCLT.satisfiesCLT_of_stationary_clt_of_uniformlyErgodic
-- status  : ACCEPTED   (prove)
-- author  : @LukeBernese
-- created : 2026-08-15T22:37:00.849773+00:00
-- url     : https://prove2.me/submissions/7fa6e181-7d05-4fab-84d9-6fc3f538b0fa

import Definitions.Def_MarkovErgodicity
import Definitions.Def_MarkovChainPathMeasure
import Definitions.Def_MarkovIterKernel
import Definitions.Def_TotalVariationDist
import Theorems.Thm_MarkovChainCLT_tvDist_chainMeasure_shift_le
import Theorems.Thm_MarkovChainCLT_abs_integral_sub_le_tvDist_of_bounded
import Theorems.Thm_MeasureTheory_tendstoInMeasure_inv_sqrt_mul_of_dominated
import Theorems.Thm_MeasureTheory_tendsto_integral_of_tendstoInMeasure_of_bounded
import Mathlib.MeasureTheory.Measure.Portmanteau

open MeasureTheory ProbabilityTheory Filter
open MarkovChainCLT
open scoped ENNReal NNReal Topology ProbabilityTheory

set_option maxHeartbeats 2000000

theorem solution {X : Type*} [MeasurableSpace X]
    (P : Kernel X X) [IsMarkovKernel P] (π : Measure X) [IsProbabilityMeasure π]
    (huni : UniformlyErgodic P π) (f : X → ℝ) (hf : Measurable f) (v : ℝ≥0)
    (hclt : TendstoInDistribution
      (fun (n : ℕ) (ω : ℕ → X) => Real.sqrt n * (sampleAvg f n ω - ∫ x, f x ∂π))
      atTop (id : ℝ → ℝ) (fun _ => chainMeasure P π) (gaussianReal 0 v)) :
    SatisfiesCLT P π f := by
  classical
  set c₀ : ℝ := ∫ x, f x ∂π with hc₀
  set T : ℕ → (ℕ → X) → ℝ :=
    fun n ω => Real.sqrt n * (sampleAvg f n ω - c₀) with hTdef
  set S : ℕ → (ℕ → X) → ℝ :=
    fun n ω => ∑ i ∈ Finset.range n, (f (ω (i + 1)) - c₀) with hSdef
  -- measurability
  have hcoord : ∀ i : ℕ, Measurable (fun ω : ℕ → X => f (ω i)) :=
    fun i => hf.comp (measurable_pi_apply i)
  have hSmeas : ∀ n, Measurable (S n) := by
    intro n
    exact Finset.measurable_sum _ (fun i _ => (hcoord (i + 1)).sub measurable_const)
  have hTmeas : ∀ n, Measurable (T n) := by
    intro n
    refine measurable_const.mul (Measurable.sub ?_ measurable_const)
    exact measurable_const.mul (Finset.measurable_sum _ (fun i _ => hcoord (i + 1)))
  -- `T n = (√n)⁻¹ • S n` and `S n = √n • T n`
  have hTS : ∀ n ω, T n ω = (Real.sqrt n)⁻¹ * S n ω := by
    intro n ω
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [hTdef, hSdef, sampleAvg]
    · have hnR : (0 : ℝ) < n := by exact_mod_cast hn
      have hsq : 0 < Real.sqrt n := Real.sqrt_pos.mpr hnR
      have e1 : Real.sqrt n * (n : ℝ)⁻¹ = (Real.sqrt n)⁻¹ := by
        rw [← div_eq_mul_inv, Real.sqrt_div_self', one_div]
      have e2 : (Real.sqrt n)⁻¹ * (n : ℝ) = Real.sqrt n := by
        rw [inv_mul_eq_div, Real.div_sqrt]
      have hsum : S n ω = (∑ i ∈ Finset.range n, f (ω (i + 1))) - (n : ℝ) * c₀ := by
        simp [hSdef, Finset.sum_sub_distrib, mul_comm]
      rw [hsum]
      simp only [hTdef, sampleAvg]
      set A : ℝ := ∑ i ∈ Finset.range n, f (ω (i + 1)) with hA
      have step1 : Real.sqrt n * ((n : ℝ)⁻¹ * A - c₀)
          = (Real.sqrt n * (n : ℝ)⁻¹) * A - Real.sqrt n * c₀ := by ring
      have step2 : (Real.sqrt n)⁻¹ * (A - (n : ℝ) * c₀)
          = (Real.sqrt n)⁻¹ * A - ((Real.sqrt n)⁻¹ * (n : ℝ)) * c₀ := by ring
      rw [step1, step2, e1, e2]
  have hST : ∀ n ω, S n ω = Real.sqrt n * T n ω := by
    intro n ω
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [hSdef]
    · have hnR : (0 : ℝ) < n := by exact_mod_cast hn
      have hsq : 0 < Real.sqrt n := Real.sqrt_pos.mpr hnR
      rw [hTS, ← mul_assoc, mul_inv_cancel₀ hsq.ne', one_mul]
  -- splitting the partial sum at time `m`
  have hSadd : ∀ (m n : ℕ) (ω : ℕ → X),
      S (m + n) ω = S m ω + S n (fun k => ω (k + m)) := by
    intro m n ω
    simp only [hSdef]
    rw [Finset.sum_range_add]
    congr 1
    refine Finset.sum_congr rfl (fun i _ => ?_)
    have : m + i + 1 = i + 1 + m := by omega
    rw [this]
  have hTdec : ∀ (m n : ℕ) (ω : ℕ → X),
      T (m + n) ω = (Real.sqrt (m + n))⁻¹ * S m ω
        + (Real.sqrt n * (Real.sqrt (m + n))⁻¹) * T n (fun k => ω (k + m)) := by
    intro m n ω
    rw [hTS, hSadd m n ω, hST n (fun k => ω (k + m))]
    push_cast
    ring
  -- now fix an initial distribution
  refine ⟨v, fun lam _ => ?_⟩
  show TendstoInDistribution T atTop (id : ℝ → ℝ) (fun _ => chainMeasure P lam)
    (gaussianReal 0 v)
  refine ⟨fun n => (hTmeas n).aemeasurable, measurable_id.aemeasurable, ?_⟩
  refine (tendsto_iff_forall_lipschitz_integral_tendsto (γ := ℕ) (Ω := ℝ)).mpr ?_
  intro F hFb hFl
  obtain ⟨Cb, hCb⟩ := hFb
  obtain ⟨Lp, hLp⟩ := hFl
  have hCb0 : 0 ≤ Cb := le_trans dist_nonneg (hCb 0 0)
  set M : ℝ := |F 0| + Cb with hMdef
  have hM0 : 0 ≤ M := by positivity
  have hFM : ∀ x, |F x| ≤ M := by
    intro x
    have h1 := hCb x 0
    rw [Real.dist_eq] at h1
    have : |F x| ≤ |F x - F 0| + |F 0| := by
      simpa using abs_add_le (F x - F 0) (F 0)
    rw [hMdef]
    linarith
  have hFcont : Continuous F := hLp.continuous
  have hFmeas : Measurable F := hFcont.measurable
  -- the two integral forms
  show Tendsto (fun i => ∫ ω, F ω ∂((chainMeasure P lam).map (T i))) atTop
    (𝓝 (∫ ω, F ω ∂((gaussianReal 0 v).map (id : ℝ → ℝ))))
  rw [integral_map measurable_id.aemeasurable hFcont.aestronglyMeasurable]
  have hgoal : ∀ k : ℕ,
      ∫ x, F x ∂((chainMeasure P lam).map (T k)) = ∫ ω, F (T k ω) ∂(chainMeasure P lam) := by
    intro k
    rw [integral_map (hTmeas k).aemeasurable hFcont.aestronglyMeasurable]
  simp only [hgoal]
  set Lval : ℝ := ∫ x, F (id x) ∂(gaussianReal 0 v) with hLval
  -- uniform ergodicity data
  obtain ⟨R, t, hR0, ht0, ht1, hrate⟩ := huni
  refine Metric.tendsto_atTop.mpr (fun ε hε => ?_)
  -- choose the burn-in `m`
  have hlim : Tendsto (fun m : ℕ => (2 * M * R) * t ^ m) atTop (𝓝 0) := by
    have := (tendsto_pow_atTop_nhds_zero_of_lt_one ht0 ht1).const_mul (2 * M * R)
    simpa using this
  obtain ⟨m, hm1, hmlt⟩ : ∃ m : ℕ, 1 ≤ m ∧ (2 * M * R) * t ^ m < ε / 3 := by
    have h1 : ∀ᶠ m : ℕ in atTop, (2 * M * R) * t ^ m < ε / 3 :=
      hlim.eventually_lt_const (by linarith)
    obtain ⟨m, hm⟩ := (h1.and (eventually_ge_atTop 1)).exists
    exact ⟨m, hm.2, hm.1⟩
  set shft : (ℕ → X) → (ℕ → X) := fun ω => fun k => ω (k + m) with hshft
  have hshftmeas : Measurable shft :=
    measurable_pi_lambda _ (fun _ => measurable_pi_apply _)
  set cs : ℕ → ℝ := fun n => Real.sqrt n * (Real.sqrt (m + n))⁻¹ with hcs
  -- `cs n → 1`
  have hcs1 : Tendsto cs atTop (𝓝 1) := by
    have hfrac : Tendsto (fun n : ℕ => (n : ℝ) / ((m : ℝ) + n)) atTop (𝓝 1) := by
      have h0 : Tendsto (fun n : ℕ => (m : ℝ) / ((m : ℝ) + n)) atTop (𝓝 0) := by
        apply Filter.Tendsto.div_atTop tendsto_const_nhds
        exact tendsto_atTop_add_const_left _ _ tendsto_natCast_atTop_atTop
      have := (tendsto_const_nhds (x := (1 : ℝ)) (f := atTop (α := ℕ))).sub h0
      rw [sub_zero] at this
      refine this.congr' ?_
      filter_upwards [eventually_ge_atTop 1] with n hn
      have hpos : (0 : ℝ) < (m : ℝ) + n := by
        have : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
        have : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
        positivity
      field_simp
      ring
    have := (Real.continuous_sqrt.tendsto (1 : ℝ)).comp hfrac
    rw [Real.sqrt_one] at this
    refine this.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hmn : (0 : ℝ) ≤ (m : ℝ) + n := by positivity
    simp only [Function.comp_apply, hcs]
    rw [Real.sqrt_div (by positivity : (0:ℝ) ≤ (n:ℝ)), div_eq_mul_inv]
  -- Slutsky on the stationary side
  have hYmeas : ∀ n : ℕ, AEMeasurable (fun _ : ℕ → X => cs n) (chainMeasure P π) :=
    fun n => measurable_const.aemeasurable
  have hYtend : TendstoInMeasure (chainMeasure P π)
      (fun (n : ℕ) (_ : ℕ → X) => cs n) atTop (fun _ => (1 : ℝ)) := by
    refine tendstoInMeasure_of_ne_top (fun δ hδ hδtop => ?_)
    have hr : 0 < δ.toReal := ENNReal.toReal_pos hδ.ne' hδtop
    obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hcs1 _ hr
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop N] with n hn
    have hlt : edist (cs n) (1 : ℝ) < δ := by
      rw [← ENNReal.ofReal_toReal hδtop, edist_lt_ofReal]
      exact hN n hn
    have : {_ω : ℕ → X | δ ≤ edist (cs n) (1 : ℝ)} = ∅ := by
      ext ω; simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_le]
      exact hlt
    rw [this, measure_empty]
  have hslut : TendstoInDistribution (fun (n : ℕ) (ω : ℕ → X) => cs n * T n ω) atTop
      (fun x : ℝ => 1 * id x) (fun _ => chainMeasure P π) (gaussianReal 0 v) :=
    hclt.continuous_comp_prodMk_of_tendstoInMeasure_const
      (g := fun p : ℝ × ℝ => p.2 * p.1) (by fun_prop) hYtend hYmeas
  have hstat : Tendsto (fun n : ℕ => ∫ ω, F (cs n * T n ω) ∂(chainMeasure P π))
      atTop (𝓝 Lval) := by
    have h1 : Tendsto
        (fun i : ℕ => ∫ ω, F ω ∂((chainMeasure P π).map (fun ω => cs i * T i ω))) atTop
        (𝓝 (∫ ω, F ω ∂((gaussianReal 0 v).map (fun x : ℝ => 1 * id x)))) :=
      tendsto_iff_forall_lipschitz_integral_tendsto.mp hslut.tendsto F ⟨Cb, hCb⟩ ⟨Lp, hLp⟩
    have hmap : ∀ k : ℕ, ∫ x, F x ∂((chainMeasure P π).map (fun ω => cs k * T k ω))
        = ∫ ω, F (cs k * T k ω) ∂(chainMeasure P π) := by
      intro k
      rw [integral_map ((hTmeas k).const_mul _).aemeasurable hFcont.aestronglyMeasurable]
    simp only [hmap] at h1
    have hlim : ∫ ω, F ω ∂((gaussianReal 0 v).map (fun x : ℝ => 1 * id x)) = Lval := by
      rw [hLval]
      rw [integral_map (by fun_prop) hFcont.aestronglyMeasurable]
      simp
    rwa [hlim] at h1
  -- total-variation comparison of the shifted `lam`-chain with the stationary chain
  have hbdmeas : ∀ n : ℕ, Measurable (fun ω : ℕ → X => F (cs n * T n ω)) :=
    fun n => hFmeas.comp ((hTmeas n).const_mul _)
  have htv : ∀ n : ℕ,
      |(∫ ω, F (cs n * T n (shft ω)) ∂(chainMeasure P lam))
        - (∫ ω, F (cs n * T n ω) ∂(chainMeasure P π))| ≤ (2 * M * R) * t ^ m := by
    intro n
    have h1 : (∫ ω, F (cs n * T n (shft ω)) ∂(chainMeasure P lam))
        = ∫ ω, F (cs n * T n ω) ∂((chainMeasure P lam).map shft) := by
      rw [integral_map hshftmeas.aemeasurable (hbdmeas n).aestronglyMeasurable]
    haveI : IsProbabilityMeasure ((chainMeasure P lam).map shft) :=
      Measure.isProbabilityMeasure_map hshftmeas.aemeasurable
    rw [h1]
    have hbase := abs_integral_sub_le_tvDist_of_bounded ((chainMeasure P lam).map shft)
      (chainMeasure P π) (fun ω => F (cs n * T n ω)) (hbdmeas n) M hM0 (fun ω => hFM _)
    have htvle : tvDist ((chainMeasure P lam).map shft) (chainMeasure P π) ≤ R * t ^ m := by
      have := tvDist_chainMeasure_shift_le P π lam m (R * t ^ m) (by positivity)
        (fun x => hrate x m hm1)
      exact this
    refine le_trans hbase ?_
    have : 2 * M * tvDist ((chainMeasure P lam).map shft) (chainMeasure P π)
        ≤ 2 * M * (R * t ^ m) := by
      exact mul_le_mul_of_nonneg_left htvle (by positivity)
    linarith [this]
  -- the negligible remainder
  set W : ℕ → (ℕ → X) → ℝ := fun n ω => cs n * S m ω with hW
  have hWdom : ∀ n ω, |W n ω| ≤ |S m ω| := by
    intro n ω
    have hle : Real.sqrt (n : ℝ) ≤ Real.sqrt ((m : ℝ) + (n : ℝ)) := by
      apply Real.sqrt_le_sqrt
      have : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
      linarith
    have hcs0 : 0 ≤ cs n := by
      simp only [hcs]
      positivity
    have hcs1' : cs n ≤ 1 := by
      simp only [hcs]
      rcases eq_or_lt_of_le (Real.sqrt_nonneg ((m : ℝ) + (n : ℝ))) with h | h
      · rw [← h, inv_zero, mul_zero]
        norm_num
      · have h1 : Real.sqrt (n : ℝ) * (Real.sqrt ((m : ℝ) + (n : ℝ)))⁻¹
            ≤ Real.sqrt ((m : ℝ) + (n : ℝ)) * (Real.sqrt ((m : ℝ) + (n : ℝ)))⁻¹ :=
          mul_le_mul_of_nonneg_right hle (by positivity)
        rwa [mul_inv_cancel₀ (ne_of_gt h)] at h1
    rw [hW, abs_mul, abs_of_nonneg hcs0]
    calc cs n * |S m ω| ≤ 1 * |S m ω| :=
          mul_le_mul_of_nonneg_right hcs1' (abs_nonneg _)
      _ = |S m ω| := one_mul _
  have hkey : TendstoInMeasure (chainMeasure P lam)
      (fun (n : ℕ) (ω : ℕ → X) => (Real.sqrt n)⁻¹ * W n ω) atTop 0 :=
    MeasureTheory.tendstoInMeasure_inv_sqrt_mul_of_dominated (chainMeasure P lam) W
      (fun ω => |S m ω|) (continuous_abs.measurable.comp (hSmeas m)) hWdom
  set G : ℕ → (ℕ → X) → ℝ :=
    fun n ω => F (T (m + n) ω) - F (cs n * T n (shft ω)) with hG
  have hGmeas : ∀ n, Measurable (G n) := by
    intro n
    exact (hFmeas.comp (hTmeas (m + n))).sub
      (hFmeas.comp (((hTmeas n).comp hshftmeas).const_mul _))
  have hGbd : ∀ n ω, |G n ω| ≤ 2 * M := by
    intro n ω
    have h1 := hFM (T (m + n) ω)
    have h2 := hFM (cs n * T n (shft ω))
    rw [hG]
    calc |F (T (m + n) ω) - F (cs n * T n (shft ω))|
        ≤ |F (T (m + n) ω)| + |F (cs n * T n (shft ω))| := abs_sub _ _
      _ ≤ 2 * M := by linarith
  have hGle : ∀ n ω, |G n ω| ≤ (Lp : ℝ) * |(Real.sqrt (m + n))⁻¹ * S m ω| := by
    intro n ω
    have hdec := hTdec m n ω
    have hdiff : T (m + n) ω - cs n * T n (shft ω) = (Real.sqrt (m + n))⁻¹ * S m ω := by
      rw [hdec, hcs, hshft]
      ring
    have := hLp.dist_le_mul (T (m + n) ω) (cs n * T n (shft ω))
    rw [Real.dist_eq, Real.dist_eq, hdiff] at this
    exact this
  have hGmeasure : TendstoInMeasure (chainMeasure P lam) G atTop 0 := by
    rw [tendstoInMeasure_iff_norm]
    intro δ hδ
    have hkey' := (tendstoInMeasure_iff_norm.mp hkey) (δ / ((Lp : ℝ) + 1)) (by positivity)
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hkey'
      (Eventually.of_forall (fun n => by simp)) ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    refine measure_mono (fun ω hω => ?_)
    simp only [Set.mem_setOf_eq, Pi.zero_apply, sub_zero, Real.norm_eq_abs] at hω ⊢
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    have hsq : 0 < Real.sqrt n := Real.sqrt_pos.mpr hnR
    have hEq : (Real.sqrt n)⁻¹ * W n ω = (Real.sqrt (m + n))⁻¹ * S m ω := by
      rw [hW, hcs, ← mul_assoc, ← mul_assoc, inv_mul_cancel₀ hsq.ne', one_mul]
    rw [hEq]
    have h1 := hGle n ω
    have h2 : (0 : ℝ) ≤ |(Real.sqrt (m + n))⁻¹ * S m ω| := abs_nonneg _
    have h3 : (Lp : ℝ) * |(Real.sqrt (m + n))⁻¹ * S m ω|
        ≤ ((Lp : ℝ) + 1) * |(Real.sqrt (m + n))⁻¹ * S m ω| := by nlinarith
    have h4 : δ ≤ ((Lp : ℝ) + 1) * |(Real.sqrt (m + n))⁻¹ * S m ω| := by linarith
    rw [div_le_iff₀ (by positivity)] at *
    nlinarith
  have hrem : Tendsto (fun n => ∫ ω, G n ω ∂(chainMeasure P lam)) atTop (𝓝 0) :=
    MeasureTheory.tendsto_integral_of_tendstoInMeasure_of_bounded (chainMeasure P lam)
      G hGmeas (2 * M) hGbd hGmeasure
  -- assemble
  obtain ⟨N1, hN1⟩ := Metric.tendsto_atTop.mp hrem (ε / 3) (by linarith)
  obtain ⟨N2, hN2⟩ := Metric.tendsto_atTop.mp hstat (ε / 3) (by linarith)
  refine ⟨m + max N1 N2, fun k hk => ?_⟩
  obtain ⟨n, rfl⟩ : ∃ n, k = m + n := ⟨k - m, by omega⟩
  have hk' : max N1 N2 ≤ n := by omega
  have hn1 : N1 ≤ n := le_trans (le_max_left _ _) hk'
  have hn2 : N2 ≤ n := le_trans (le_max_right _ _) hk'
  have hint1 : Integrable (fun ω => F (T (m + n) ω)) (chainMeasure P lam) :=
    ⟨(hFmeas.comp (hTmeas (m + n))).aestronglyMeasurable,
      HasFiniteIntegral.of_bounded (C := M) (ae_of_all _ (fun ω => by
        simpa [Real.norm_eq_abs] using hFM _))⟩
  have hint2 : Integrable (fun ω => F (cs n * T n (shft ω))) (chainMeasure P lam) :=
    ⟨(hFmeas.comp (((hTmeas n).comp hshftmeas).const_mul _)).aestronglyMeasurable,
      HasFiniteIntegral.of_bounded (C := M) (ae_of_all _ (fun ω => by
        simpa [Real.norm_eq_abs] using hFM _))⟩
  have hsplit : ∫ ω, G n ω ∂(chainMeasure P lam)
      = (∫ ω, F (T (m + n) ω) ∂(chainMeasure P lam))
        - ∫ ω, F (cs n * T n (shft ω)) ∂(chainMeasure P lam) := by
    rw [hG, integral_sub hint1 hint2]
  have e1 := hN1 n hn1
  have e2 := hN2 n hn2
  rw [Real.dist_eq, sub_zero] at e1
  rw [Real.dist_eq] at e2
  rw [hsplit] at e1
  have e3 := htv n
  rw [Real.dist_eq]
  have := abs_sub_abs_le_abs_sub
    ((∫ ω, F (T (m + n) ω) ∂(chainMeasure P lam)) - Lval) 0
  calc |(∫ ω, F (T (m + n) ω) ∂(chainMeasure P lam)) - Lval|
      ≤ |(∫ ω, F (T (m + n) ω) ∂(chainMeasure P lam))
          - ∫ ω, F (cs n * T n (shft ω)) ∂(chainMeasure P lam)|
        + |(∫ ω, F (cs n * T n (shft ω)) ∂(chainMeasure P lam))
          - ∫ ω, F (cs n * T n ω) ∂(chainMeasure P π)|
        + |(∫ ω, F (cs n * T n ω) ∂(chainMeasure P π)) - Lval| := by
        have := abs_sub_le
          (∫ ω, F (T (m + n) ω) ∂(chainMeasure P lam))
          (∫ ω, F (cs n * T n (shft ω)) ∂(chainMeasure P lam))
          Lval
        have h2 := abs_sub_le
          (∫ ω, F (cs n * T n (shft ω)) ∂(chainMeasure P lam))
          (∫ ω, F (cs n * T n ω) ∂(chainMeasure P π))
          Lval
        linarith
    _ < ε := by linarith
