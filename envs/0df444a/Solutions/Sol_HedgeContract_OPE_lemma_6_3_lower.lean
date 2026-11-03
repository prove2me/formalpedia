-- Prove2me | solution 1 for HedgeContract.OPE.lemma_6_3_lower
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-03T04:18:16.703847+00:00
-- url     : https://prove2.me/submissions/727d420a-693e-4b3b-b1f4-c189bc4027a7

import Mathlib
import Definitions.Def_HedgeContract_OPE_Model
set_option autoImplicit false
open HedgeContract.OPE MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal

namespace HedgeLowerAux


lemma riemann_tendsto (f : ℝ → ℝ) (hf : Continuous f) (t : ℝ) (ht : 0 ≤ t) :
    Tendsto (fun n : ℕ => ∑ k ∈ Finset.range n, (t / n) * f (k * t / n)) atTop
      (𝓝 (∫ s in (0:ℝ)..t, f s)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have huc : UniformContinuousOn f (Set.Icc 0 t) :=
    isCompact_Icc.uniformContinuousOn_of_continuous hf.continuousOn
  rw [Metric.uniformContinuousOn_iff] at huc
  obtain ⟨η, hη, hηf⟩ := huc (ε / (t + 1)) (by positivity)
  obtain ⟨N, hN⟩ := exists_nat_gt (t / η)
  refine ⟨N + 1, fun n hn => ?_⟩
  have hn0 : 0 < n := by omega
  have hnpos : (0:ℝ) < n := by exact_mod_cast hn0
  have htn : t / n < η := by
    rw [div_lt_iff₀ hnpos]
    rw [div_lt_iff₀ hη] at hN
    have : (N:ℝ) + 1 ≤ n := by exact_mod_cast hn
    nlinarith
  set a : ℕ → ℝ := fun k => k * t / n with ha
  have hsplit : ∑ k ∈ Finset.range n, ∫ s in a k..a (k+1), f s = ∫ s in a 0..a n, f s :=
    intervalIntegral.sum_integral_adjacent_intervals (fun k _ => hf.intervalIntegrable _ _)
  have ha0 : a 0 = 0 := by simp [a]
  have han : a n = t := by simp only [a]; field_simp
  rw [ha0, han] at hsplit
  rw [Real.dist_eq, ← hsplit, ← Finset.sum_sub_distrib]
  have hlen : ∀ k : ℕ, a (k+1) - a k = t / n := by intro k; simp only [a]; push_cast; ring
  have hstep : ∀ k ∈ Finset.range n,
      |t / n * f (k * t / n) - ∫ s in a k..a (k+1), f s| ≤ ε / (t + 1) * (t / n) := by
    intro k hk
    have hkn : k < n := Finset.mem_range.mp hk
    have hc : t / n * f (k * t / n) = ∫ _ in a k..a (k+1), f (k * t / n) := by
      rw [intervalIntegral.integral_const, hlen, smul_eq_mul]
    rw [hc, ← intervalIntegral.integral_sub intervalIntegrable_const (hf.intervalIntegrable _ _)]
    have hle : a k ≤ a (k+1) := by have := hlen k; have : 0 ≤ t / n := by positivity
                                   linarith
    have hak0 : 0 ≤ a k := by simp only [a]; positivity
    have hak1 : a (k+1) ≤ t := by
      simp only [a]; rw [div_le_iff₀ hnpos]; push_cast
      have : (k:ℝ) + 1 ≤ n := by exact_mod_cast hkn
      nlinarith
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := a k) (b := a (k+1))
      (C := ε / (t + 1)) (f := fun s => f (k * t / n) - f s) ?_
    · simp only [Real.norm_eq_abs] at this
      rw [hlen k, abs_of_nonneg (a := t / n) (by positivity)] at this
      exact this
    · intro s hs
      rw [Set.uIoc_of_le hle] at hs
      rw [Real.norm_eq_abs]
      have h1 : a k ∈ Set.Icc 0 t := ⟨hak0, by linarith⟩
      have h2 : s ∈ Set.Icc 0 t := ⟨by linarith [hs.1], by linarith [hs.2]⟩
      have hd : dist (a k) s < η := by
        rw [Real.dist_eq, abs_sub_comm, abs_of_nonneg (by linarith [hs.1])]
        linarith [hs.2, hlen k]
      exact (hηf _ h1 _ h2 hd).le
  calc |∑ k ∈ Finset.range n, (t / n * f (k * t / n) - ∫ s in a k..a (k+1), f s)|
      ≤ ∑ k ∈ Finset.range n, |t / n * f (k * t / n) - ∫ s in a k..a (k+1), f s| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _k ∈ Finset.range n, ε / (t + 1) * (t / n) := Finset.sum_le_sum hstep
    _ = ε * (t / (t + 1)) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; field_simp
    _ < ε := by
        have : t / (t + 1) < 1 := by rw [div_lt_one (by linarith)]; linarith
        nlinarith

lemma ode_key (φ : ℝ → ℝ) (hφ : Continuous φ) (r g0 : ℝ) (hr : r ≠ 0) (Y : ℝ → ℝ)
    (hY : ∀ s, 0 ≤ s → Y s = φ s + r * Real.exp (r * s) *
      (∫ x in (0:ℝ)..s, Real.exp (-r * x) * φ x) + g0 * (Real.exp (r * s) - 1) / r)
    (t : ℝ) (ht : 0 ≤ t) :
    IntegrableOn (fun s => r * Y s + g0) (Set.Icc 0 t) ∧
      ∫ s in Set.Icc 0 t, (r * Y s + g0) = Y t - φ t := by
  set F : ℝ → ℝ := fun x => Real.exp (-r * x) * φ x with hF
  have hFc : Continuous F := by fun_prop
  set U : ℝ → ℝ := fun s => ∫ x in (0:ℝ)..s, F x with hU
  have hUd : ∀ s, HasDerivAt U (F s) s := fun s =>
    (hFc.integral_hasStrictDerivAt 0 s).hasDerivAt
  have hUc : Continuous U := continuous_iff_continuousAt.2 fun s => (hUd s).continuousAt
  set G : ℝ → ℝ := fun s => r * Real.exp (r * s) * U s + g0 * (Real.exp (r * s) - 1) / r
  set D : ℝ → ℝ := fun s => r * (φ s + r * Real.exp (r * s) * U s +
      g0 * (Real.exp (r * s) - 1) / r) + g0 with hD
  have hDc : Continuous D := by fun_prop
  have hGd : ∀ s, HasDerivAt G (D s) s := by
    intro s
    have he : HasDerivAt (fun s => Real.exp (r * s)) (Real.exp (r * s) * r) s := by
      have := ((hasDerivAt_id s).const_mul r).exp
      simpa using this
    have h1 := ((he.const_mul r).mul (hUd s))
    have h2 := ((he.sub_const 1).const_mul g0).div_const r
    have h3 : HasDerivAt G (r * (Real.exp (r * s) * r) * U s + r * Real.exp (r * s) * F s +
        g0 * (Real.exp (r * s) * r) / r) s := h1.add h2
    refine h3.congr_deriv ?_
    simp only [hD, hF]
    simp only [neg_mul]
    have hee : Real.exp (r * s) * Real.exp (-(r * s)) = 1 := by
      rw [← Real.exp_add]; simp
    field_simp
    linear_combination (r * φ s) * hee
  have hint : ∫ s in (0:ℝ)..t, D s = G t - G 0 :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hGd s) (hDc.intervalIntegrable _ _)
  have hG0 : G 0 = 0 := by simp [G, U]
  have hcongr : Set.EqOn (fun s => r * Y s + g0) D (Set.Icc 0 t) := by
    intro s hs; dsimp only; rw [hY s hs.1]
  refine ⟨(hDc.integrableOn_Icc).congr_fun hcongr.symm measurableSet_Icc, ?_⟩
  rw [setIntegral_congr_fun measurableSet_Icc hcongr, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le ht, hint, hG0, sub_zero, hY t ht]
  simp only [G, U, F]; ring



noncomputable def phi {Ω : Type*} (P : Params) (B : ℝ≥0 → Ω → Fin 2 → ℝ) (ω : Ω) (s : ℝ) : ℝ :=
  P.σ * P.Γlo * (B s.toNNReal ω 0 - B 0 ω 0) +
    Real.sqrt (1 - P.ρ ^ 2) * P.ψ * P.Zlo * (B s.toNNReal ω 1 - B 0 ω 1)

noncomputable def uu {Ω : Type*} (P : Params) (B : ℝ≥0 → Ω → Fin 2 → ℝ) (t : ℝ) (ω : Ω) : ℝ :=
  limUnder atTop (fun n : ℕ => ∑ k ∈ Finset.range n,
    (t / n) * (Real.exp (-P.r * (k * t / n)) * phi P B ω (k * t / n)))

noncomputable def YY {Ω : Type*} (P : Params) (B : ℝ≥0 → Ω → Fin 2 → ℝ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  phi P B ω t + P.r * Real.exp (P.r * t) * uu P B t ω +
    g P P.Zlo P.Γlo * (Real.exp (P.r * t) - 1) / P.r

noncomputable def lump {Ω : Type*} (P : Params) (B : ℝ≥0 → Ω → Fin 2 → ℝ) (y : ℝ) :
    Contract Ω where
  Z := fun _ _ => P.Zlo
  ζ := fun _ _ => P.Γlo
  I := fun _ _ => y
  Y := YY P B
  J₀ := fun t ω => P.σ * P.Γlo * (B t ω 0 - B 0 ω 0)
  J₁ := fun t ω => Real.sqrt (1 - P.ρ ^ 2) * P.ψ * P.Zlo * (B t ω 1 - B 0 ω 1)

lemma YY_zero {Ω : Type*} (P : Params) (B : ℝ≥0 → Ω → Fin 2 → ℝ) (ω : Ω) : YY P B 0 ω = 0 := by
  have hu : uu P B 0 ω = 0 := by
    unfold uu
    simp only [zero_div, mul_zero, zero_mul, Finset.sum_const_zero]
    exact tendsto_const_nhds.limUnder_eq
  simp [YY, phi, hu]

lemma tau_lump {Ω : Type*} (P : Params) (B : ℝ≥0 → Ω → Fin 2 → ℝ) (y : ℝ) (ω : Ω) :
    (lump P B y).τ ω = 0 := by
  refine le_antisymm (sInf_le ⟨0, ?_, by simp⟩) zero_le
  show YY P B 0 ω ≤ 0
  rw [YY_zero]

lemma phi_coe {Ω : Type*} (P : Params) (B : ℝ≥0 → Ω → Fin 2 → ℝ) (ω : Ω) (t : ℝ≥0) :
    phi P B ω t = (lump P B 0).J₀ t ω + (lump P B 0).J₁ t ω := by
  simp [phi, lump]

lemma B_meas {Ω : Type*} [MeasurableSpace Ω] {P₀ : Measure Ω} {B : ℝ≥0 → Ω → Fin 2 → ℝ}
    (hB : Peng1990.SMP.IsStdBrownian P₀ B) (j : Fin 2) {s t : ℝ≥0} (hst : s ≤ t) :
    Measurable[Peng1990.SMP.brownianFiltration hB t] (fun ω => B s ω j) := by
  have h : StronglyMeasurable[Peng1990.SMP.brownianFiltration hB s] (B s) :=
    Filtration.stronglyAdapted_natural (fun t => (hB.meas t).stronglyMeasurable) s
  exact (measurable_pi_apply j).comp
    ((h.mono ((Peng1990.SMP.brownianFiltration hB).mono hst)).measurable)

noncomputable def simpleConst {Ω : Type*} [MeasurableSpace Ω] (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›)
    (P₀ : Measure Ω) [IsProbabilityMeasure P₀] (T : ℝ≥0) (c : ℝ) :
    Peng1990.SMP.SimpleIntegrand 𝓕 P₀ T where
  r := 1
  t := ![0, T]
  mono := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all
  start := rfl
  finish := rfl
  ξ := fun _ _ => c
  meas := fun _ => stronglyMeasurable_const
  sq := by simp [lintegral_const]

lemma ito_const {Ω : Type*} [MeasurableSpace Ω] {P₀ : Measure Ω} [IsProbabilityMeasure P₀]
    {B : ℝ≥0 → Ω → Fin 2 → ℝ} (hB : Peng1990.SMP.IsStdBrownian P₀ B) (j : Fin 2) (c : ℝ)
    (T : ℝ≥0) :
    Peng1990.SMP.IsItoIntegral (Peng1990.SMP.brownianFiltration hB) P₀ T
      (fun t ω => B t ω j) (fun _ _ => c) (fun t ω => c * (B t ω j - B 0 ω j)) := by
  refine ⟨⟨isStronglyProgressive_const _ c, ?_⟩, ?_, ?_⟩
  · simp [lintegral_const]
    exact ENNReal.mul_lt_top (by simp) (by simp)
  · intro t
    exact (((B_meas hB j le_rfl).sub (B_meas hB j zero_le)).const_mul c).stronglyMeasurable
  · refine ⟨fun _ => simpleConst _ P₀ T c, ?_, ?_⟩
    · have h0 : ∀ ω : Ω, ∫⁻ s in Set.Icc (0:ℝ) T,
          ‖(simpleConst (Peng1990.SMP.brownianFiltration hB) P₀ T c).eval s.toNNReal ω - c‖ₑ ^ 2
            = 0 := by
        intro ω
        rw [← setLIntegral_congr Ioc_ae_eq_Icc]
        rw [setLIntegral_congr_fun measurableSet_Ioc (g := fun _ => 0) ?_]
        · simp
        · intro s hs
          have h1 : (0 : ℝ≥0) < s.toNNReal := Real.toNNReal_pos.2 hs.1
          have h2 : s.toNNReal ≤ T := (Real.toNNReal_le_iff_le_coe).2 hs.2
          have he : (simpleConst (Peng1990.SMP.brownianFiltration hB) P₀ T c).eval
              s.toNNReal ω = c := by
            change (∑ i : Fin 1, if (![0, T] : Fin 2 → ℝ≥0) i.castSucc < s.toNNReal ∧
              s.toNNReal ≤ (![0, T] : Fin 2 → ℝ≥0) i.succ then c else 0) = c
            simp [h1, h2]
          simp [he]
      simp only [h0, lintegral_zero]
      exact tendsto_const_nhds
    · intro t ht
      have h0 : ∀ ω : Ω, (simpleConst (Peng1990.SMP.brownianFiltration hB) P₀ T c).integral
          (fun t ω => B t ω j) t ω = c * (B t ω j - B 0 ω j) := by
        intro ω
        change (∑ i : Fin 1, c * (B (min ((![0, T] : Fin 2 → ℝ≥0) i.succ) t) ω j -
          B (min ((![0, T] : Fin 2 → ℝ≥0) i.castSucc) t) ω j)) = _
        simp [min_eq_right ht]
      simp only [h0, sub_self, enorm_zero]
      simp

lemma path_lump {Ω : Type*} (P : Params) (B : ℝ≥0 → Ω → Fin 2 → ℝ) (y : ℝ) (ω : Ω) (t : ℝ) :
    (lump P B y).paymentPath ω t = if t < 0 then 0 else y := by
  simp [Contract.paymentPath, lump]

lemma mono_lump {Ω : Type*} (P : Params) (B : ℝ≥0 → Ω → Fin 2 → ℝ) {y : ℝ} (hy : 0 ≤ y)
    (ω : Ω) : Monotone ((lump P B y).paymentPath ω) := by
  intro a b hab
  rw [path_lump, path_lump]
  split_ifs <;> linarith

lemma payMeas_lump {Ω : Type*} (P : Params) (B : ℝ≥0 → Ω → Fin 2 → ℝ) {y : ℝ} (hy : 0 ≤ y)
    (ω : Ω) : (lump P B y).paymentMeasure ω {0} = ENNReal.ofReal y := by
  have hm := mono_lump P B hy ω
  rw [Contract.paymentMeasure, dif_pos hm, StieltjesFunction.measure_singleton,
    Monotone.stieltjesFunction_eq]
  have hr : Function.rightLim ((lump P B y).paymentPath ω) 0 = y := by
    apply rightLim_eq_of_tendsto
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
    rw [path_lump, if_neg (not_lt.2 ht.le)]
  have hl : Function.leftLim hm.stieltjesFunction 0 = 0 := by
    apply leftLim_eq_of_tendsto
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with x (hx : x < 0)
    rw [Monotone.stieltjesFunction_eq]
    symm
    apply rightLim_eq_of_tendsto
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [Ioo_mem_nhdsGT hx] with t ht
    rw [path_lump, if_pos ht.2]
  rw [hr, hl, sub_zero]

lemma payment_lump {Ω : Type*} (P : Params) (B : ℝ≥0 → Ω → Fin 2 → ℝ) {y : ℝ} (hy : 0 ≤ y)
    (ω : Ω) : (lump P B y).payment P ω = y := by
  have hS : {t : ℝ | 0 ≤ t ∧ ENNReal.ofReal t ≤ (lump P B y).τ ω} = {0} := by
    ext t
    simp only [tau_lump, Set.mem_setOf_eq, Set.mem_singleton_iff, nonpos_iff_eq_zero,
      ENNReal.ofReal_eq_zero]
    constructor
    · rintro ⟨h1, h2⟩; linarith
    · rintro rfl; simp
  rw [Contract.payment, hS, integral_singleton, measureReal_def, payMeas_lump P B hy,
    ENNReal.toReal_ofReal hy]
  simp

lemma pathPayoff_lump {Ω : Type*} (P : Params) (B : ℝ≥0 → Ω → Fin 2 → ℝ) {y : ℝ}
    (hy : 0 ≤ y) (ω : Ω) : (lump P B y).pathPayoff P ω = Wlow P y := by
  have hS : {t : ℝ | 0 ≤ t ∧ ENNReal.ofReal t < (lump P B y).τ ω} = ∅ := by
    ext t; simp [tau_lump]
  rw [Contract.pathPayoff, hS, payment_lump P B hy, tau_lump]
  simp [Wlow]; ring

lemma phi_meas {Ω : Type*} [MeasurableSpace Ω] {P₀ : Measure Ω} (P : Params)
    {B : ℝ≥0 → Ω → Fin 2 → ℝ} (hB : Peng1990.SMP.IsStdBrownian P₀ B) {s : ℝ} {t : ℝ≥0}
    (hs : s.toNNReal ≤ t) :
    Measurable[Peng1990.SMP.brownianFiltration hB t] (fun ω => phi P B ω s) := by
  unfold phi
  exact (((B_meas hB 0 hs).sub (B_meas hB 0 zero_le)).const_mul _).add
    (((B_meas hB 1 hs).sub (B_meas hB 1 zero_le)).const_mul _)

lemma YY_adapted {Ω : Type*} [MeasurableSpace Ω] {P₀ : Measure Ω} (P : Params)
    {B : ℝ≥0 → Ω → Fin 2 → ℝ} (hB : Peng1990.SMP.IsStdBrownian P₀ B) :
    StronglyAdapted (Peng1990.SMP.brownianFiltration hB) (YY P B) := by
  intro t
  have hterm : ∀ n : ℕ, Measurable[Peng1990.SMP.brownianFiltration hB t] (fun ω =>
      ∑ k ∈ Finset.range n, ((t : ℝ) / n) *
        (Real.exp (-P.r * (k * (t : ℝ) / n)) * phi P B ω (k * (t : ℝ) / n))) := by
    intro n
    refine Finset.measurable_sum _ (fun k hk => ?_)
    have hkn : k < n := Finset.mem_range.mp hk
    have hle : (k * (t : ℝ) / n).toNNReal ≤ t := by
      rw [Real.toNNReal_le_iff_le_coe]
      have hnpos : (0:ℝ) < n := by exact_mod_cast (by omega : 0 < n)
      rw [div_le_iff₀ hnpos]
      have : (k:ℝ) ≤ n := by exact_mod_cast hkn.le
      have ht0 : (0:ℝ) ≤ t := t.2
      nlinarith
    exact ((phi_meas P hB hle).const_mul _).const_mul _
  have hu : StronglyMeasurable[Peng1990.SMP.brownianFiltration hB t]
      (fun ω => uu P B t ω) := by
    let : MeasurableSpace Ω := Peng1990.SMP.brownianFiltration hB t
    exact StronglyMeasurable.limUnder (fun n => (hterm n).stronglyMeasurable)
  have hphi : Measurable[Peng1990.SMP.brownianFiltration hB t]
      (fun ω => phi P B ω t) := phi_meas P hB (by simp)
  unfold YY
  exact ((hphi.add (hu.measurable.const_mul _)).add_const _).stronglyMeasurable

lemma path_ok {Ω : Type*} (P : Params) (B : ℝ≥0 → Ω → Fin 2 → ℝ) (hr : P.r ≠ 0) (y : ℝ)
    (ω : Ω) (h0 : Continuous (fun t => B t ω 0)) (h1 : Continuous (fun t => B t ω 1))
    (t : ℝ≥0) :
    IntegrableOn (fun s : ℝ => P.r * (lump P B y).Y s.toNNReal ω +
        g P ((lump P B y).Z s.toNNReal ω) ((lump P B y).ζ s.toNNReal ω)) (Set.Icc 0 (t : ℝ)) ∧
      (lump P B y).Y t ω = y + (∫ s in Set.Icc (0 : ℝ) (t : ℝ),
        P.r * (lump P B y).Y s.toNNReal ω +
          g P ((lump P B y).Z s.toNNReal ω) ((lump P B y).ζ s.toNNReal ω)) -
        (lump P B y).I t ω + (lump P B y).J₀ t ω + (lump P B y).J₁ t ω := by
  have hφc : Continuous (phi P B ω) := by
    unfold phi
    have c0 : Continuous (fun s : ℝ => B s.toNNReal ω 0) := h0.comp continuous_real_toNNReal
    have c1 : Continuous (fun s : ℝ => B s.toNNReal ω 1) := h1.comp continuous_real_toNNReal
    fun_prop
  have hFc : Continuous (fun x : ℝ => Real.exp (-P.r * x) * phi P B ω x) := by fun_prop
  have huu : ∀ s : ℝ, 0 ≤ s →
      uu P B s ω = ∫ x in (0:ℝ)..s, Real.exp (-P.r * x) * phi P B ω x := fun s hs =>
    (riemann_tendsto _ hFc s hs).limUnder_eq
  have hY : ∀ s : ℝ, 0 ≤ s → YY P B s.toNNReal ω = phi P B ω s + P.r * Real.exp (P.r * s) *
      (∫ x in (0:ℝ)..s, Real.exp (-P.r * x) * phi P B ω x) +
        g P P.Zlo P.Γlo * (Real.exp (P.r * s) - 1) / P.r := by
    intro s hs
    unfold YY
    rw [Real.coe_toNNReal _ hs, huu s hs]
  obtain ⟨hI, hE⟩ := ode_key (phi P B ω) hφc P.r (g P P.Zlo P.Γlo) hr
    (fun s => YY P B s.toNNReal ω) hY t t.2
  refine ⟨hI, ?_⟩
  change YY P B t ω = y + (∫ s in Set.Icc (0 : ℝ) (t : ℝ),
        (P.r * YY P B s.toNNReal ω + g P P.Zlo P.Γlo)) - y +
      P.σ * P.Γlo * (B t ω 0 - B 0 ω 0) +
      Real.sqrt (1 - P.ρ ^ 2) * P.ψ * P.Zlo * (B t ω 1 - B 0 ω 1)
  rw [hE]
  simp only [Real.toNNReal_coe, phi]
  ring

lemma setS_lump {Ω : Type*} (P : Params) (B : ℝ≥0 → Ω → Fin 2 → ℝ) (y : ℝ) (ω : Ω) :
    {t : ℝ | 0 ≤ t ∧ ENNReal.ofReal t ≤ (lump P B y).τ ω} = {0} := by
  ext t
  simp only [tau_lump, Set.mem_setOf_eq, Set.mem_singleton_iff, nonpos_iff_eq_zero,
    ENNReal.ofReal_eq_zero]
  constructor
  · rintro ⟨h1, h2⟩; linarith
  · rintro rfl; simp

theorem lower_main (P : Params) (hP : P.Standing)
    {Ω : Type*} [MeasurableSpace Ω] (P₀ : MeasureTheory.Measure Ω)
    [MeasureTheory.IsProbabilityMeasure P₀]
    (B : ℝ≥0 → Ω → Fin 2 → ℝ) (hB : Peng1990.SMP.IsStdBrownian P₀ B)
    (h1 : P.δ < P.r) :
    ∀ y : ℝ, 0 ≤ y →
      ∃ C : Contract Ω, C.Admissible P P₀ B hB y ∧ C.payoff P P₀ = Wlow P y := by
  intro y hy
  obtain ⟨-, -, -, -, -, hδ, -, hZ, hΓ, -, -⟩ := hP
  have hr : P.r ≠ 0 := by linarith
  have hpp : (fun ω => (lump P B y).pathPayoff P ω) = fun _ => Wlow P y :=
    funext (pathPayoff_lump P B hy)
  refine ⟨lump P B y, ?_, ?_⟩
  · refine ⟨isStronglyProgressive_const _ _, isStronglyProgressive_const _ _,
      fun _ _ => ⟨⟨le_rfl, hZ⟩, ⟨le_rfl, hΓ⟩⟩, stronglyAdapted_const _ y, YY_adapted P hB,
      mono_lump P B hy, fun _ _ => continuousWithinAt_const, fun _ => hy,
      fun T => ito_const hB 0 (P.σ * P.Γlo) T,
      fun T => ito_const hB 1 (Real.sqrt (1 - P.ρ ^ 2) * P.ψ * P.Zlo) T, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · filter_upwards [(hB.brownian 0).cont, (hB.brownian 1).cont] with ω c0 c1
      refine ⟨?_, ?_, fun t => path_ok P B hr y ω c0 c1 t⟩
      · show Continuous (fun t => P.σ * P.Γlo * (B t ω 0 - B 0 ω 0))
        fun_prop
      · show Continuous (fun t => Real.sqrt (1 - P.ρ ^ 2) * P.ψ * P.Zlo * (B t ω 1 - B 0 ω 1))
        fun_prop
    · intro T
      have h0 : (fun ω => Real.exp (-P.δ * (T : ℝ)) * (lump P B y).Y T ω *
          (if (T : ℝ≥0∞) ≤ (lump P B y).τ ω then (1 : ℝ) else 0)) = fun _ => 0 := by
        funext ω
        rw [tau_lump]
        by_cases hT : T = 0
        · subst hT; simp [show (lump P B y).Y 0 ω = 0 from YY_zero P B ω]
        · simp [hT]
      rw [h0]; exact integrable_zero _ _ _
    · have h0 : ∀ T : ℝ≥0, (∫ ω, Real.exp (-P.δ * (T : ℝ)) * (lump P B y).Y T ω *
          (if (T : ℝ≥0∞) ≤ (lump P B y).τ ω then (1 : ℝ) else 0) ∂P₀) = 0 := by
        intro T
        refine integral_eq_zero_of_ae (Eventually.of_forall fun ω => ?_)
        simp only [Pi.zero_apply]
        rw [tau_lump]
        by_cases hT : T = 0
        · subst hT; simp [show (lump P B y).Y 0 ω = 0 from YY_zero P B ω]
        · simp [hT]
      simp only [h0]
      exact tendsto_const_nhds
    · refine Eventually.of_forall fun ω => ?_
      rw [setS_lump]
      exact integrableOn_singleton (hx := by rw [payMeas_lump P B hy]; exact ENNReal.ofReal_lt_top)
    · rw [funext (payment_lump P B hy)]; exact integrable_const _
    · rw [hpp]; exact integrable_const _
  · rw [Contract.payoff, hpp]; simp

end HedgeLowerAux

theorem solution (P : HedgeContract.OPE.Params) (hP : P.Standing)
    {Ω : Type*} [MeasurableSpace Ω] (P₀ : MeasureTheory.Measure Ω)
    [MeasureTheory.IsProbabilityMeasure P₀]
    (B : ℝ≥0 → Ω → Fin 2 → ℝ) (hB : Peng1990.SMP.IsStdBrownian P₀ B)
    (h1 : P.δ < P.r) (h2 : 0 ≤ HedgeContract.OPE.netSup P) (h6 : P.δ * P.Φ ≤ P.mu) :
    ∀ y : ℝ, 0 ≤ y →
      ∃ C : HedgeContract.OPE.Contract Ω, C.Admissible P P₀ B hB y ∧
        C.payoff P P₀ = HedgeContract.OPE.Wlow P y :=
  HedgeLowerAux.lower_main P hP P₀ B hB h1

