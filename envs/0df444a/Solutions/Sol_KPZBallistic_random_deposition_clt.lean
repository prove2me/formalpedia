-- Prove2me | solution 1 for KPZBallistic.random_deposition_clt
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T21:36:48.23137+00:00
-- url     : https://prove2.me/submissions/43831b82-2a01-4c42-b011-f009d64c31d7

import Mathlib
import Definitions.Def_KPZBallistic_Defs


open MeasureTheory ProbabilityTheory Filter Topology Set Real

namespace KPA

lemma int_exp (f : ℝ → ℝ) : ∫ x, f x ∂(expMeasure 1) = ∫ x in Ioi 0, exp (-x) * f x := by
  rw [expMeasure, gammaMeasure, integral_withDensity_eq_integral_toReal_smul
    (show Measurable (gammaPDF 1 1) from (measurable_gammaPDFReal 1 1).ennreal_ofReal) (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top)),
    ← integral_Ici_eq_integral_Ioi, ← integral_indicator measurableSet_Ici]
  congr 1; ext x
  by_cases hx : 0 ≤ x
  · rw [indicator_of_mem (by simpa using hx), gammaPDF_of_nonneg hx, ENNReal.toReal_ofReal
      (by positivity)]
    simp
  · rw [indicator_of_notMem (by simpa using hx), gammaPDF_of_neg (by linarith)]
    simp

lemma gi (s : ℝ) (hs : 0 < s) : IntegrableOn (fun x : ℝ => exp (-x) * x ^ (s - 1)) (Ioi 0) :=
  Real.GammaIntegral_convergent hs

lemma i1 : IntegrableOn (fun x : ℝ => exp (-x)) (Ioi 0) := by
  refine (gi 1 one_pos).congr_fun (fun x _ => by simp) measurableSet_Ioi

lemma i2 : IntegrableOn (fun x : ℝ => exp (-x) * x) (Ioi 0) := by
  refine (gi 2 two_pos).congr_fun (fun x _ => by norm_num) measurableSet_Ioi

lemma i3 : IntegrableOn (fun x : ℝ => exp (-x) * x ^ 2) (Ioi 0) := by
  refine (gi 3 (by norm_num)).congr_fun (fun x hx => ?_) measurableSet_Ioi
  simp only
  rw [show (3:ℝ) - 1 = ((2:ℕ):ℝ) by norm_num, Real.rpow_natCast]

lemma v1 : ∫ x in Ioi (0:ℝ), exp (-x) = 1 := by
  have := Real.Gamma_eq_integral one_pos
  simp only [sub_self, Real.rpow_zero, mul_one, Real.Gamma_one] at this
  exact this.symm

lemma v2 : ∫ x in Ioi (0:ℝ), exp (-x) * x = 1 := by
  have := Real.Gamma_eq_integral two_pos
  rw [Real.Gamma_two] at this
  rw [this]; congr 1; ext x; norm_num

lemma v3 : ∫ x in Ioi (0:ℝ), exp (-x) * x ^ 2 = 2 := by
  have := Real.Gamma_eq_integral (s := 3) (by norm_num)
  rw [show (3:ℝ) = 2 + 1 by norm_num, Real.Gamma_add_one (by norm_num), Real.Gamma_two] at this
  rw [show (2:ℝ) + 1 - 1 = ((2:ℕ):ℝ) by norm_num] at this
  simp only [Real.rpow_natCast] at this
  linarith

lemma mean0 : ∫ x, (1 - x) ∂(expMeasure 1) = 0 := by
  rw [int_exp]
  have : ∀ x, exp (-x) * (1 - x) = exp (-x) - exp (-x) * x := fun x => by ring
  simp_rw [this]
  rw [integral_sub i1 i2, v1, v2, sub_self]

lemma mean1 : ∫ x, x ∂(expMeasure 1) = 1 := by
  rw [int_exp]; exact v2

lemma sq1 : ∫ x, (1 - x) ^ 2 ∂(expMeasure 1) = 1 := by
  rw [int_exp]
  have : ∀ x, exp (-x) * (1 - x) ^ 2 = (exp (-x) - 2 * (exp (-x) * x)) + exp (-x) * x ^ 2 :=
    fun x => by ring
  simp_rw [this]
  have h12 : IntegrableOn (fun x : ℝ => exp (-x) - 2 * (exp (-x) * x)) (Ioi 0) :=
    i1.sub (i2.const_mul 2)
  rw [integral_add (f := fun x : ℝ => exp (-x) - 2 * (exp (-x) * x)) h12 i3,
    integral_sub (f := fun x : ℝ => exp (-x)) i1 (i2.const_mul 2),
    integral_const_mul, v1, v2, v3]; norm_num

lemma nonneg_ae : ∀ᵐ x ∂(expMeasure 1), 0 ≤ x := by
  rw [expMeasure, gammaMeasure, ae_withDensity_iff (show Measurable (gammaPDF 1 1) from (measurable_gammaPDFReal 1 1).ennreal_ofReal)]
  refine ae_of_all _ (fun x hx => ?_)
  by_contra h
  exact hx (gammaPDF_of_neg (by linarith))

end KPA

open MeasureTheory ProbabilityTheory Filter Topology Set Real

namespace KPB


lemma G_single (x : ℝ) : (gaussianReal 0 1) {x} = 0 := by
  have := nullSingletonClass_gaussianReal (μ := 0) (v := 1) one_ne_zero
  exact measure_singleton x

lemma G_Iio (x : ℝ) : (gaussianReal 0 1) (Iio x) = (gaussianReal 0 1) (Iic x) := by
  rw [← Iic_sdiff_right, measure_sdiff_null (G_single x)]

lemma cdf_cont (x : ℝ) : ContinuousAt (cdf (gaussianReal 0 1)) x := by
  have hl : Function.leftLim (cdf (gaussianReal 0 1)) x = cdf (gaussianReal 0 1) x := by
    have h1 := (cdf (gaussianReal 0 1)).measure_Iio (tendsto_cdf_atBot _) x
    have h2 := (cdf (gaussianReal 0 1)).measure_Iic (tendsto_cdf_atBot _) x
    have h3 : (gaussianReal 0 1) (Iic x) = (cdf (gaussianReal 0 1)).measure (Iic x) := by
      rw [measure_cdf]
    rw [measure_cdf, G_Iio, h3, h2] at h1
    have hnn : 0 ≤ Function.leftLim (cdf (gaussianReal 0 1)) x :=
      le_trans (cdf_nonneg _ (x - 1)) ((monotone_cdf (gaussianReal 0 1)).le_leftLim (by linarith))
    simp only [sub_zero] at h1
    exact ((ENNReal.ofReal_eq_ofReal_iff (cdf_nonneg _ x) hnn).1 h1).symm
  rw [continuousAt_iff_continuous_left_right]
  refine ⟨?_, (cdf (gaussianReal 0 1)).right_continuous x⟩
  rw [← continuousWithinAt_Iio_iff_Iic]
  exact (Monotone.continuousWithinAt_Iio_iff_leftLim_eq (monotone_cdf (gaussianReal 0 1))).2 hl

lemma G_real_Iio (x : ℝ) : (gaussianReal 0 1).real (Iio x) = cdf (gaussianReal 0 1) x := by
  rw [cdf_eq_real, measureReal_def, measureReal_def, G_Iio]

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- Portmanteau at half-lines. -/
lemma port (Z : ℕ → Ω → ℝ) (hZm : ∀ n, Measurable (Z n))
    (h : TendstoInDistribution Z atTop id (fun _ => P) (gaussianReal 0 1)) (c : ℝ) :
    Tendsto (fun n => P.real {ω | Z n ω < c}) atTop (𝓝 (cdf (gaussianReal 0 1) c)) := by
  have key := ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto' h.tendsto
    (E := Iio c) (by simp [G_single])
  simp only [ProbabilityMeasure.coe_mk] at key
  rw [Measure.map_id] at key
  rw [← G_real_Iio, measureReal_def]
  have key2 := (ENNReal.tendsto_toReal (measure_ne_top _ _)).comp key
  refine key2.congr (fun n => ?_)
  simp only [Function.comp_apply, measureReal_def]
  rw [Measure.map_apply (hZm n) measurableSet_Iio]
  rfl

/-- Moving thresholds. -/
lemma moving {α : Type*} {l : Filter α} (Z : ℕ → Ω → ℝ) (hZm : ∀ n, Measurable (Z n))
    (h : TendstoInDistribution Z atTop id (fun _ => P) (gaussianReal 0 1))
    (n : α → ℕ) (hn : Tendsto n l atTop) (c : α → ℝ) (x : ℝ) (hc : Tendsto c l (𝓝 x)) :
    Tendsto (fun a => P.real {ω | Z (n a) ω < c a}) l (𝓝 (cdf (gaussianReal 0 1) x)) := by
  rw [Metric.tendsto_nhds]
  intro δ hδ
  obtain ⟨ε, hε, hεF⟩ := Metric.continuousAt_iff.1 (cdf_cont x) (δ / 2) (by linarith)
  have hp := @hεF (x + ε / 2) (by rw [Real.dist_eq]; rw [abs_of_pos (by linarith)]; linarith)
  have hm := @hεF (x - ε / 2) (by rw [Real.dist_eq, abs_of_neg (by linarith)]; linarith)
  rw [Real.dist_eq] at hp hm
  have Lp := Metric.tendsto_nhds.1 ((port Z hZm h (x + ε / 2)).comp hn) (δ / 2) (by linarith)
  have Lm := Metric.tendsto_nhds.1 ((port Z hZm h (x - ε / 2)).comp hn) (δ / 2) (by linarith)
  have hcl : ∀ᶠ a in l, |c a - x| < ε / 2 := by
    have := Metric.tendsto_nhds.1 hc (ε / 2) (by linarith)
    simpa [Real.dist_eq] using this
  filter_upwards [Lp, Lm, hcl] with a ha1 ha2 ha3
  simp only [Function.comp_apply, Real.dist_eq] at ha1 ha2
  rw [Real.dist_eq]
  have hc1 : c a < x + ε / 2 := by linarith [(abs_lt.1 ha3).2]
  have hc2 : x - ε / 2 < c a := by linarith [(abs_lt.1 ha3).1]
  have s1 : P.real {ω | Z (n a) ω < c a} ≤ P.real {ω | Z (n a) ω < x + ε / 2} :=
    measureReal_mono (fun ω (hω : Z (n a) ω < c a) => show Z (n a) ω < x + ε / 2 by linarith)
  have s2 : P.real {ω | Z (n a) ω < x - ε / 2} ≤ P.real {ω | Z (n a) ω < c a} :=
    measureReal_mono (fun ω (hω : Z (n a) ω < x - ε / 2) => show Z (n a) ω < c a by linarith)
  rw [abs_lt] at ha1 ha2 hp hm ⊢
  constructor <;> linarith [ha1.1, ha1.2, ha2.1, ha2.2, hp.1, hp.2, hm.1, hm.2]

end KPB

open MeasureTheory ProbabilityTheory Filter Topology Set Real

namespace KPC

/-- Renewal inversion for a monotone unbounded sequence. -/
lemma ncard_le_iff (A : ℕ → ℝ) (hA : Monotone A) (hU : ∀ t, ∃ n, t < A n) (t : ℝ) (m : ℕ) :
    {n : ℕ | A n ≤ t}.ncard ≤ m ↔ t < A m := by
  constructor
  · intro h
    by_contra hc
    push Not at hc
    obtain ⟨N, hN⟩ := hU t
    have hfin : {n : ℕ | A n ≤ t} ⊆ (Finset.range N : Set ℕ) := by
      intro n hn
      simp only [Finset.coe_range, mem_Iio]
      by_contra h'
      push Not at h'
      have := hA h'
      simp only [mem_ofPred_eq] at hn
      linarith
    have hsub : (Finset.range (m + 1) : Set ℕ) ⊆ {n : ℕ | A n ≤ t} := by
      intro n hn
      simp only [Finset.coe_range, mem_Iio] at hn
      simp only [mem_ofPred_eq]
      exact le_trans (hA (by omega)) hc
    have := Set.ncard_le_ncard hsub ((Finset.range N).finite_toSet.subset hfin)
    rw [Set.ncard_coe_finset, Finset.card_range] at this
    omega
  · intro h
    have hsub : {n : ℕ | A n ≤ t} ⊆ (Finset.range m : Set ℕ) := by
      intro n hn
      simp only [Finset.coe_range, mem_Iio]
      by_contra h'
      push Not at h'
      have := hA h'
      simp only [mem_ofPred_eq] at hn
      linarith
    have := Set.ncard_le_ncard hsub (Finset.range m).finite_toSet
    rwa [Set.ncard_coe_finset, Finset.card_range] at this

lemma ev_large (x : ℝ) : Tendsto (fun t : ℝ => t + x * √t) atTop atTop := by
  have h : ∀ᶠ t in atTop, t / 2 ≤ t + x * √t := by
    filter_upwards [eventually_ge_atTop (4 * x ^ 2 + 1)] with t ht
    have ht0 : 0 ≤ t := by nlinarith
    have hs := Real.sq_sqrt ht0
    have hs0 := Real.sqrt_nonneg t
    have h2 : 2 * |x| ≤ √t := by
      rw [show 2 * |x| = √((2 * |x|) ^ 2) by rw [Real.sqrt_sq (by positivity)]]
      apply Real.sqrt_le_sqrt
      nlinarith [sq_abs x]
    have : -(x * √t) ≤ |x| * √t := by
      have := mul_le_mul_of_nonneg_right (neg_abs_le x) hs0; linarith
    nlinarith
  exact tendsto_atTop_mono' atTop h (tendsto_id.atTop_div_const two_pos)

/-- Deterministic: the moving threshold tends to `x`. -/
lemma thr_tendsto (x : ℝ) :
    Tendsto (fun t : ℝ => (((⌊t + x * √t⌋₊ + 1 : ℕ) : ℝ) - t) / (√(((⌊t + x * √t⌋₊ + 1 : ℕ) : ℝ))))
      atTop (𝓝 x) := by
  set K : ℝ := 1 + |x| * (|x| + 1)
  have hN : Tendsto (fun t : ℝ => (((⌊t + x * √t⌋₊ + 1 : ℕ) : ℝ))) atTop atTop := by
    refine tendsto_atTop_mono' atTop (Eventually.of_forall fun t => ?_) (ev_large x)
    push_cast
    by_cases h : 0 ≤ t + x * √t
    · linarith [Nat.lt_floor_add_one (t + x * √t)]
    · push Not at h; have := Nat.cast_nonneg (α := ℝ) ⌊t + x * √t⌋₊; linarith
  have hinv : Tendsto (fun t : ℝ => K / (√(((⌊t + x * √t⌋₊ + 1 : ℕ) : ℝ)))) atTop (𝓝 0) := by
    have := (tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp hN)).const_mul K
    simpa [div_eq_mul_inv] using this
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hinv
  filter_upwards [eventually_ge_atTop 1, (ev_large x).eventually (eventually_ge_atTop 0)]
    with t ht1 ht2
  set N : ℝ := ((⌊t + x * √t⌋₊ + 1 : ℕ) : ℝ) with hNdef
  have hfl1 : (⌊t + x * √t⌋₊ : ℝ) ≤ t + x * √t := Nat.floor_le ht2
  have hfl2 := Nat.lt_floor_add_one (t + x * √t)
  have hN1 : t + x * √t < N := by rw [hNdef]; push_cast; linarith
  have hN2 : N ≤ t + x * √t + 1 := by rw [hNdef]; push_cast; linarith
  have hNpos : 0 < N := by rw [hNdef]; positivity
  set s := √t with hsdef
  have hs1 : 1 ≤ s := by rw [hsdef]; rw [show (1:ℝ) = √1 by simp]; exact Real.sqrt_le_sqrt ht1
  have hss : s ^ 2 = t := Real.sq_sqrt (by linarith)
  set r := √N with hrdef
  have hr0 : 0 < r := Real.sqrt_pos.2 hNpos
  have hrr : r ^ 2 = N := Real.sq_sqrt hNpos.le
  rw [Real.norm_eq_abs, show (N - t) / r - x = (N - t - x * r) / r by field_simp]
  rw [abs_div, abs_of_pos hr0]
  apply div_le_div_of_nonneg_right _ hr0.le
  -- |N - t - x r| ≤ K
  have e1 : |N - t - x * s| ≤ 1 := by rw [abs_le]; constructor <;> linarith
  have e2 : |s - r| ≤ |x| + 1 := by
    have hsr : 0 < s + r := by linarith
    have : s - r = (t - N) / (s + r) := by
      field_simp; nlinarith
    rw [this, abs_div, abs_of_pos hsr, div_le_iff₀ hsr]
    have : |t - N| ≤ |x| * s + 1 := by
      rw [abs_le]; constructor
      · nlinarith [neg_abs_le x, le_abs_self x]
      · nlinarith [neg_abs_le x, le_abs_self x]
    nlinarith [abs_nonneg x]
  calc |N - t - x * r| = |(N - t - x * s) + x * (s - r)| := by ring_nf
    _ ≤ |N - t - x * s| + |x * (s - r)| := abs_add_le _ _
    _ ≤ 1 + |x| * (|x| + 1) := by
        rw [abs_mul]; gcongr
    _ = K := rfl

end KPC

open MeasureTheory ProbabilityTheory Filter Topology Set Real
open KPZBallistic

namespace KPD

theorem main {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (τ : ℤ → ℕ → Ω → ℝ) (hτ : IsPoissonClocks P τ) (x : ℝ) :
    Tendsto (fun t : ℝ => P.real {ω | ((rdHeight τ t 0 ω : ℝ) - t) / Real.sqrt t ≤ x})
      atTop (𝓝 ((gaussianReal 0 1).real (Set.Iic x))) := by
  set X : ℕ → Ω → ℝ := fun k ω => 1 - τ 0 k ω with hX
  have hτm : ∀ k, Measurable (τ 0 k) := fun k => hτ.measurable 0 k
  have hXm : ∀ k, Measurable (X k) := fun k => measurable_const.sub (hτm k)
  have hind0 : iIndepFun (fun k : ℕ => τ 0 k) P :=
    hτ.indep.precomp (g := fun k : ℕ => ((0:ℤ), k)) (fun a b h => by simpa using h)
  have hind : iIndepFun X P :=
    hind0.comp (fun _ y => 1 - y) (fun _ => measurable_const.sub measurable_id)
  have hidT : ∀ k, IdentDistrib (τ 0 k) (τ 0 0) P P := fun k =>
    ⟨(hτm k).aemeasurable, (hτm 0).aemeasurable, by rw [hτ.law, hτ.law]⟩
  have hident : ∀ k, IdentDistrib (X k) (X 0) P P := fun k =>
    (hidT k).comp (u := fun y => 1 - y) (measurable_const.sub measurable_id)
  have hint : ∀ f : ℝ → ℝ, Continuous f → ∫ ω, f (τ 0 0 ω) ∂P = ∫ y, f y ∂(expMeasure 1) := by
    intro f hf
    rw [← hτ.law 0 0, integral_map (hτm 0).aemeasurable hf.aestronglyMeasurable]
  have h0 : P[X 0] = 0 := by
    rw [hX]; simp only
    rw [hint (fun y => 1 - y) (by fun_prop), KPA.mean0]
  have h1 : P[X 0 ^ 2] = 1 := by
    rw [hX]; simp only [Pi.pow_apply]
    rw [hint (fun y => (1 - y) ^ 2) (by fun_prop), KPA.sq1]
  have hclt := tendstoInDistribution_inv_sqrt_mul_sum (Y := id) (P' := gaussianReal 0 1)
    HasLaw.id h0 h1 hind hident
  set Z : ℕ → Ω → ℝ := fun n ω => (√n)⁻¹ * ∑ k ∈ Finset.range n, X k ω with hZ
  have hZm : ∀ n, Measurable (Z n) := fun n =>
    measurable_const.mul (Finset.measurable_sum _ (fun k _ => hXm k))
  -- good event
  have hnn : ∀ᵐ ω ∂P, ∀ k, 0 ≤ τ 0 k ω := by
    rw [ae_all_iff]; intro k
    exact ae_of_ae_map (hτm k).aemeasurable (by rw [hτ.law]; exact KPA.nonneg_ae)
  have hmean : ∫ ω, τ 0 0 ω ∂P = 1 := by
    have := hint id continuous_id
    simp only [id] at this
    rw [this]; exact KPA.mean1
  have hslln := strong_law_ae (fun k => τ 0 k) (Integrable.of_integral_ne_zero (by rw [hmean]; norm_num))
    (fun i j hij => hind0.indepFun hij) hidT
  have hgood : ∀ᵐ ω ∂P, (∀ k, 0 ≤ τ 0 k ω) ∧ ∀ t : ℝ, ∃ n, t < arrivalTime τ 0 n ω := by
    filter_upwards [hnn, hslln] with ω hω1 hω2
    refine ⟨hω1, fun t => ?_⟩
    rw [hmean] at hω2
    have ev := (hω2.eventually (lt_mem_nhds (by norm_num : (1/2:ℝ) < 1))).and
      (eventually_ge_atTop (⌈2 * |t|⌉₊ + 1))
    obtain ⟨n, hn1, hn2⟩ := ev.exists
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    refine ⟨m, ?_⟩
    simp only [smul_eq_mul] at hn1
    have hpos : (0:ℝ) < ((m + 1 : ℕ) : ℝ) := by positivity
    rw [lt_inv_mul_iff₀ hpos] at hn1
    have hc : (2 * |t| : ℝ) ≤ ⌈2 * |t|⌉₊ := Nat.le_ceil _
    have : ((⌈2 * |t|⌉₊ + 1 : ℕ) : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := by exact_mod_cast hn2
    push_cast at this hn1
    unfold arrivalTime
    have := le_abs_self t
    linarith
  -- monotone arrival times
  have hmono : ∀ ω, (∀ k, 0 ≤ τ 0 k ω) → Monotone (fun n => arrivalTime τ 0 n ω) := by
    intro ω h
    refine monotone_nat_of_le_succ (fun n => ?_)
    simp only [arrivalTime]
    rw [Finset.sum_range_succ _ (n + 1)]
    linarith [h (n + 1)]
  set nn : ℝ → ℕ := fun t => ⌊t + x * √t⌋₊ + 1 with hnn_def
  set cc : ℝ → ℝ := fun t => ((nn t : ℝ) - t) / √(nn t : ℝ) with hcc
  have hnn_t : Tendsto nn atTop atTop :=
    tendsto_atTop_mono (fun t => Nat.le_succ _) (tendsto_nat_floor_atTop.comp (KPC.ev_large x))
  have hmov := KPB.moving Z hZm hclt nn hnn_t cc x (KPC.thr_tendsto x)
  rw [← cdf_eq_real]
  refine hmov.congr' ?_
  filter_upwards [eventually_gt_atTop 0, (KPC.ev_large x).eventually (eventually_ge_atTop 0)]
    with t ht0 ht1
  apply measureReal_congr
  rw [Filter.eventuallyEq_set]
  filter_upwards [hgood] with ω hω
  show _ ↔ _
  have hpos : (0:ℝ) < (nn t : ℝ) := by rw [hnn_def]; positivity
  have hsq : 0 < √(nn t : ℝ) := Real.sqrt_pos.2 hpos
  have hZv : Z (nn t) ω = ((nn t : ℝ) - arrivalTime τ 0 (nn t - 1) ω) / √(nn t : ℝ) := by
    rw [hZ, hX]; simp only
    rw [div_eq_inv_mul, Finset.sum_sub_distrib]
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one, arrivalTime]
    congr 3
  rw [hZv, hcc]; simp only
  rw [div_lt_div_iff_of_pos_right hsq, sub_lt_sub_iff_left, div_le_iff₀ (Real.sqrt_pos.2 ht0)]
  have key := KPC.ncard_le_iff (fun n => arrivalTime τ 0 n ω) (hmono ω hω.1) hω.2 t (nn t - 1)
  rw [show nn t - 1 = ⌊t + x * √t⌋₊ by show ⌊t + x * √t⌋₊ + 1 - 1 = _; omega] at key ⊢
  rw [← key, rdHeight, Nat.le_floor_iff ht1]
  constructor <;> intro h <;> linarith

end KPD

open MeasureTheory ProbabilityTheory Filter Topology

theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (τ : ℤ → ℕ → Ω → ℝ) (hτ : KPZBallistic.IsPoissonClocks P τ) (x : ℝ) :
    Tendsto (fun t : ℝ => P.real {ω | ((KPZBallistic.rdHeight τ t 0 ω : ℝ) - t) / Real.sqrt t ≤ x})
      atTop (𝓝 ((gaussianReal 0 1).real (Set.Iic x))) :=
  KPD.main P τ hτ x
