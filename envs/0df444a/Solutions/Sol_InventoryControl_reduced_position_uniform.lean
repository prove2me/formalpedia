-- Prove2me | solution 1 for InventoryControl.reduced_position_uniform
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-27T19:55:24.755854+00:00
-- url     : https://prove2.me/submissions/cb0544f1-d1ae-40f9-a9f4-765c28386140

import Mathlib
import Definitions.Def_InventoryControl_rqPolicy

set_option autoImplicit false

open Filter Topology in
lemma p404_sqrt_tendsto : Tendsto Nat.sqrt atTop atTop :=
  tendsto_atTop_atTop.2 fun b => ⟨b ^ 2, fun _ hn => Nat.le_sqrt'.2 hn⟩

open Filter Topology in
lemma p404_ratio : Tendsto (fun k : ℕ => (((k + 1) ^ 2 : ℕ) : ℝ) / ((k ^ 2 : ℕ) : ℝ)) atTop (𝓝 1) := by
  have h1 : Tendsto (fun k : ℕ => (1 + 1 / (k : ℝ)) ^ 2) atTop (𝓝 ((1 + 0) ^ 2)) :=
    (tendsto_const_nhds.add tendsto_one_div_atTop_nhds_zero_nat).pow 2
  rw [show ((1:ℝ) + 0) ^ 2 = 1 by norm_num] at h1
  refine h1.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with k hk
  have hk' : (k : ℝ) ≠ 0 := by
    have : (0:ℝ) < k := by exact_mod_cast hk
    exact this.ne'
  push_cast
  field_simp

open Filter Topology Finset in
lemma p404_interp (z : ℕ → ℂ) (b : ℕ → ℝ) (β : ℝ)
    (hb : ∀ m, ‖z m‖ ≤ b m)
    (hbconv : Tendsto (fun n : ℕ => (∑ m ∈ range n, b m) / (n : ℝ)) atTop (𝓝 β))
    (hsq : Tendsto (fun k : ℕ => (∑ m ∈ range (k ^ 2), z m) / ((k ^ 2 : ℕ) : ℂ)) atTop (𝓝 0)) :
    Tendsto (fun n : ℕ => (∑ m ∈ range n, z m) / (n : ℂ)) atTop (𝓝 0) := by
  have hb0 : ∀ m, 0 ≤ b m := fun m => (norm_nonneg _).trans (hb m)
  have hg1 : Tendsto (fun k : ℕ => (k + 1) ^ 2) atTop atTop :=
    tendsto_atTop_atTop.2 fun c => ⟨c, fun k hk => by nlinarith⟩
  have hg2 : Tendsto (fun k : ℕ => k ^ 2) atTop atTop :=
    tendsto_atTop_atTop.2 fun c => ⟨c, fun k hk => by nlinarith⟩
  have h1 := hbconv.comp hg1
  have h2 := hbconv.comp hg2
  have hv : Tendsto (fun k : ℕ => ((∑ m ∈ range ((k + 1) ^ 2), b m) - ∑ m ∈ range (k ^ 2), b m)
      / ((k ^ 2 : ℕ) : ℝ)) atTop (𝓝 0) := by
    have h3 := (h1.mul p404_ratio).sub h2
    rw [mul_one, sub_self] at h3
    refine h3.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with k hk
    have hk1 : ((k ^ 2 : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (pow_ne_zero 2 (by omega))
    have hk2 : (((k + 1) ^ 2 : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (pow_ne_zero 2 (Nat.succ_ne_zero k))
    simp only [Function.comp]
    field_simp
    try ring
  have hu : Tendsto (fun k : ℕ => ‖(∑ m ∈ range (k ^ 2), z m) / ((k ^ 2 : ℕ) : ℂ)‖
      + ((∑ m ∈ range ((k + 1) ^ 2), b m) - ∑ m ∈ range (k ^ 2), b m) / ((k ^ 2 : ℕ) : ℝ))
      atTop (𝓝 0) := by
    have := hsq.norm.add hv
    rwa [norm_zero, add_zero] at this
  refine squeeze_zero_norm' ?_ (hu.comp p404_sqrt_tendsto)
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hk2 : n.sqrt ^ 2 ≤ n := Nat.sqrt_le' n
  have hk3 : n < (n.sqrt + 1) ^ 2 := Nat.lt_succ_sqrt' n
  have hk1 : 1 ≤ n.sqrt := Nat.le_sqrt'.2 (by simpa using hn)
  have hkpos : (0:ℝ) < ((n.sqrt ^ 2 : ℕ) : ℝ) := by exact_mod_cast pow_pos hk1 2
  have hkn : ((n.sqrt ^ 2 : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast hk2
  have hIco : ‖∑ m ∈ Ico (n.sqrt ^ 2) n, z m‖
      ≤ (∑ m ∈ range ((n.sqrt + 1) ^ 2), b m) - ∑ m ∈ range (n.sqrt ^ 2), b m := by
    calc ‖∑ m ∈ Ico (n.sqrt ^ 2) n, z m‖ ≤ ∑ m ∈ Ico (n.sqrt ^ 2) n, ‖z m‖ := norm_sum_le _ _
      _ ≤ ∑ m ∈ Ico (n.sqrt ^ 2) n, b m := sum_le_sum fun m _ => hb m
      _ ≤ ∑ m ∈ Ico (n.sqrt ^ 2) ((n.sqrt + 1) ^ 2), b m :=
          sum_le_sum_of_subset_of_nonneg (Ico_subset_Ico_right hk3.le) (fun m _ _ => hb0 m)
      _ = _ := by
          rw [← sum_range_add_sum_Ico b (show n.sqrt ^ 2 ≤ (n.sqrt + 1) ^ 2 by nlinarith)]
          ring
  have hsplit : ∑ m ∈ range n, z m
      = ∑ m ∈ range (n.sqrt ^ 2), z m + ∑ m ∈ Ico (n.sqrt ^ 2) n, z m :=
    (sum_range_add_sum_Ico z hk2).symm
  have hA : ‖∑ m ∈ range n, z m‖ ≤ ‖∑ m ∈ range (n.sqrt ^ 2), z m‖
      + ((∑ m ∈ range ((n.sqrt + 1) ^ 2), b m) - ∑ m ∈ range (n.sqrt ^ 2), b m) := by
    rw [hsplit]; exact (norm_add_le _ _).trans (by linarith [hIco])
  simp only [Function.comp, norm_div, Complex.norm_natCast]
  calc ‖∑ m ∈ range n, z m‖ / (n : ℝ) ≤ ‖∑ m ∈ range n, z m‖ / ((n.sqrt ^ 2 : ℕ) : ℝ) :=
        div_le_div_of_nonneg_left (norm_nonneg _) hkpos hkn
    _ ≤ (‖∑ m ∈ range (n.sqrt ^ 2), z m‖
      + ((∑ m ∈ range ((n.sqrt + 1) ^ 2), b m) - ∑ m ∈ range (n.sqrt ^ 2), b m))
        / ((n.sqrt ^ 2 : ℕ) : ℝ) := div_le_div_of_nonneg_right hA hkpos.le
    _ = _ := by rw [add_div]

open MeasureTheory Filter Topology Finset in
lemma p404_L2 {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (Z : ℕ → Ω → ℂ) (C : ℝ) (hmeas : ∀ m, Measurable (Z m))
    (hsq : ∀ m, Integrable (fun ω => ‖Z m ω‖ ^ 2) P)
    (hC : ∀ m, ∫ ω, ‖Z m ω‖ ^ 2 ∂P ≤ C)
    (horth : ∀ m m', m < m' → ∫ ω, Z m ω * (starRingEnd ℂ) (Z m' ω) ∂P = 0) (n : ℕ) :
    Integrable (fun ω => ‖∑ m ∈ range n, Z m ω‖ ^ 2) P ∧
      ∫ ω, ‖∑ m ∈ range n, Z m ω‖ ^ 2 ∂P ≤ n * C := by
  have hcross : ∀ m m', Integrable (fun ω => Z m ω * (starRingEnd ℂ) (Z m' ω)) P := by
    intro m m'
    refine Integrable.mono' (((hsq m).add (hsq m')).div_const 2) ?_ ?_
    · exact ((hmeas m).mul (Complex.continuous_conj.measurable.comp (hmeas m'))).aestronglyMeasurable
    · refine Eventually.of_forall fun ω => ?_
      rw [norm_mul, Complex.norm_conj]
      simp only [Pi.add_apply]
      nlinarith [sq_nonneg (‖Z m ω‖ - ‖Z m' ω‖), norm_nonneg (Z m ω), norm_nonneg (Z m' ω)]
  induction n with
  | zero => simp
  | succ n ih =>
    obtain ⟨hi, hle⟩ := ih
    have hexp : ∀ ω, ‖∑ m ∈ range (n + 1), Z m ω‖ ^ 2 = ‖∑ m ∈ range n, Z m ω‖ ^ 2 + ‖Z n ω‖ ^ 2
        + 2 * (∑ m ∈ range n, Z m ω * (starRingEnd ℂ) (Z n ω)).re := by
      intro ω
      rw [sum_range_succ, ← sum_mul]
      simp only [Complex.sq_norm]
      exact Complex.normSq_add _ _
    have hint_re : Integrable (fun ω => (∑ m ∈ range n, Z m ω * (starRingEnd ℂ) (Z n ω)).re) P :=
      (integrable_finsetSum (range n) fun m _ => hcross m n).re
    have hI1 : Integrable (fun ω => ‖∑ m ∈ range n, Z m ω‖ ^ 2 + ‖Z n ω‖ ^ 2) P := hi.add (hsq n)
    have hI2 : Integrable (fun ω => 2 * (∑ m ∈ range n, Z m ω * (starRingEnd ℂ) (Z n ω)).re) P :=
      hint_re.const_mul 2
    have h0 : ∫ ω, (∑ m ∈ range n, Z m ω * (starRingEnd ℂ) (Z n ω)).re ∂P = 0 := by
      have h1 : ∫ ω, ∑ m ∈ range n, Z m ω * (starRingEnd ℂ) (Z n ω) ∂P = 0 := by
        rw [integral_finsetSum _ fun m _ => hcross m n]
        exact sum_eq_zero fun m hm => horth m n (mem_range.1 hm)
      have h2 := integral_re (integrable_finsetSum (range n) fun m _ => hcross m n) (μ := P)
      rw [h1] at h2
      simpa using h2
    refine ⟨?_, ?_⟩
    · simp_rw [hexp]
      exact hI1.add hI2
    · have : ∫ ω, ‖∑ m ∈ range (n + 1), Z m ω‖ ^ 2 ∂P
          = ∫ ω, ‖∑ m ∈ range n, Z m ω‖ ^ 2 ∂P + ∫ ω, ‖Z n ω‖ ^ 2 ∂P := by
        simp_rw [hexp]
        rw [integral_add hI1 hI2, integral_add hi (hsq n), integral_const_mul, h0]
        ring
      rw [this]; push_cast; linarith [hC n]

open MeasureTheory Filter Topology Finset in
lemma p404_ae_sq {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (Z : ℕ → Ω → ℂ) (C : ℝ) (hmeas : ∀ m, Measurable (Z m))
    (hsq : ∀ m, Integrable (fun ω => ‖Z m ω‖ ^ 2) P)
    (hC : ∀ m, ∫ ω, ‖Z m ω‖ ^ 2 ∂P ≤ C)
    (horth : ∀ m m', m < m' → ∫ ω, Z m ω * (starRingEnd ℂ) (Z m' ω) ∂P = 0) :
    ∀ᵐ ω ∂P, Tendsto (fun k : ℕ => (∑ m ∈ range (k ^ 2), Z m ω) / ((k ^ 2 : ℕ) : ℂ))
      atTop (𝓝 0) := by
  have hL2 := p404_L2 Z C hmeas hsq hC horth
  have hC0 : 0 ≤ C := (integral_nonneg fun ω => by positivity).trans (hC 0)
  set e : ℕ → Ω → ENNReal := fun k ω =>
    ENNReal.ofReal (‖(∑ m ∈ range (k ^ 2), Z m ω) / ((k ^ 2 : ℕ) : ℂ)‖ ^ 2) with he
  have hemeas : ∀ k, Measurable (e k) := by
    intro k
    exact ENNReal.measurable_ofReal.comp
      (((Finset.measurable_sum _ fun m _ => hmeas m).div_const _).norm.pow_const 2)
  have hle : ∀ k, ∫⁻ ω, e k ω ∂P ≤ ENNReal.ofReal (C / (k : ℝ) ^ 2) := by
    intro k
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp [he]
    have hkpos : (0:ℝ) < ((k ^ 2 : ℕ) : ℝ) := by exact_mod_cast pow_pos hk 2
    have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
    have hpt : ∀ ω, e k ω = ENNReal.ofReal (‖∑ m ∈ range (k ^ 2), Z m ω‖ ^ 2
        / ((k ^ 2 : ℕ) : ℝ) ^ 2) := by
      intro ω
      simp only [he, norm_div, Complex.norm_natCast, div_pow]
    simp_rw [hpt]
    rw [← ofReal_integral_eq_lintegral_ofReal ((hL2 (k ^ 2)).1.div_const _)
      (Eventually.of_forall fun ω => by positivity)]
    apply ENNReal.ofReal_le_ofReal
    rw [integral_div, div_le_iff₀ (by positivity)]
    calc ∫ ω, ‖∑ m ∈ range (k ^ 2), Z m ω‖ ^ 2 ∂P ≤ ((k ^ 2 : ℕ) : ℝ) * C := (hL2 (k ^ 2)).2
      _ = C / (k:ℝ) ^ 2 * ((k ^ 2 : ℕ) : ℝ) ^ 2 := by
        push_cast
        rw [div_mul_eq_mul_div, eq_div_iff (pow_ne_zero 2 hk')]
        ring
  have hsum : ∑' k, ∫⁻ ω, e k ω ∂P ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hle)
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun k => by positivity)]
    · exact ENNReal.ofReal_ne_top
    · exact ((Real.summable_one_div_nat_pow.2 one_lt_two).mul_left C).congr fun k => by ring
  have hae : ∀ᵐ ω ∂P, ∑' k, e k ω < ⊤ := by
    refine ae_lt_top' (Measurable.ennreal_tsum hemeas).aemeasurable ?_
    rw [lintegral_tsum fun k => (hemeas k).aemeasurable]
    exact hsum
  filter_upwards [hae] with ω hω
  have h1 := ENNReal.tendsto_atTop_zero_of_tsum_ne_top hω.ne
  have h2 : Tendsto (fun k => (e k ω).toReal) atTop (𝓝 0) := by
    have h5 := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h1
    simpa only [ENNReal.toReal_zero, Function.comp_def] using h5
  have h3 : Tendsto (fun k : ℕ => ‖(∑ m ∈ range (k ^ 2), Z m ω) / ((k ^ 2 : ℕ) : ℂ)‖)
      atTop (𝓝 0) := by
    have h4 := h2.sqrt
    rw [Real.sqrt_zero] at h4
    refine h4.congr fun k => ?_
    simp only [he]
    rw [ENNReal.toReal_ofReal (by positivity), Real.sqrt_sq (norm_nonneg _)]
  exact tendsto_zero_iff_norm_tendsto_zero.2 h3

open MeasureTheory Filter Topology Finset in
lemma p404_slln_orth {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (Z : ℕ → Ω → ℂ) (C : ℝ) (hmeas : ∀ m, Measurable (Z m))
    (hsq : ∀ m, Integrable (fun ω => ‖Z m ω‖ ^ 2) P)
    (hC : ∀ m, ∫ ω, ‖Z m ω‖ ^ 2 ∂P ≤ C)
    (horth : ∀ m m', m < m' → ∫ ω, Z m ω * (starRingEnd ℂ) (Z m' ω) ∂P = 0)
    (b : ℕ → Ω → ℝ) (β : Ω → ℝ)
    (hb : ∀ᵐ ω ∂P, (∀ m, ‖Z m ω‖ ≤ b m ω) ∧
      Tendsto (fun n : ℕ => (∑ m ∈ range n, b m ω) / (n : ℝ)) atTop (𝓝 (β ω))) :
    ∀ᵐ ω ∂P, Tendsto (fun n : ℕ => (∑ m ∈ range n, Z m ω) / (n : ℂ)) atTop (𝓝 0) := by
  filter_upwards [p404_ae_sq Z C hmeas hsq hC horth, hb] with ω h1 h2
  exact p404_interp (fun m => Z m ω) (fun m => b m ω) (β ω) h2.1 h2.2 h1

open Filter Topology Finset in
lemma p404_const_avg (c : ℝ) :
    Tendsto (fun n : ℕ => (∑ m ∈ range n, c) / (n : ℝ)) atTop (𝓝 c) := by
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_div_cancel_left₀ _ hn']

open Filter Topology Finset in
lemma p404_event_avg (a b : ℕ → ℂ) (n0 : ℕ) (hab : ∀ m, n0 ≤ m → a m = b m) (L : ℂ)
    (hb : Tendsto (fun n : ℕ => (∑ m ∈ range n, b m) / (n : ℂ)) atTop (𝓝 L)) :
    Tendsto (fun n : ℕ => (∑ m ∈ range n, a m) / (n : ℂ)) atTop (𝓝 L) := by
  have hc : Tendsto (fun n : ℕ => (∑ m ∈ range n0, (a m - b m)) / (n : ℂ)) atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat _
  have := hb.add hc
  rw [add_zero] at this
  refine this.congr' ?_
  filter_upwards [eventually_ge_atTop n0] with n hn
  have e : ∑ m ∈ range n, (a m - b m) = ∑ m ∈ range n0, (a m - b m) := by
    refine (sum_subset (range_mono hn) fun m hm hm' => ?_).symm
    simp only [mem_range, not_lt] at hm hm'
    rw [hab m hm', sub_self]
  rw [← e, sum_sub_distrib]
  ring


-- ============ Part B: probability facts ============

noncomputable def p404_ch (θ x : ℝ) : ℂ := Complex.exp (↑(θ * x) * Complex.I)

lemma p404_ch_norm (θ x : ℝ) : ‖p404_ch θ x‖ = 1 := Complex.norm_exp_ofReal_mul_I _

lemma p404_ch_add (θ x y : ℝ) : p404_ch θ (x + y) = p404_ch θ x * p404_ch θ y := by
  unfold p404_ch
  rw [← Complex.exp_add]; congr 1; push_cast; ring

lemma p404_ch_zero (θ : ℝ) : p404_ch θ 0 = 1 := by simp [p404_ch]

lemma p404_ch_meas (θ : ℝ) : Measurable (fun x => p404_ch θ x) :=
  (by unfold p404_ch; fun_prop : Continuous (fun x => p404_ch θ x)).measurable

open MeasureTheory ProbabilityTheory InventoryControl in
noncomputable def p404_mu {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (X : CompoundPoissonDemand P) : ℝ :=
  ∫ x, x ∂(expMeasure X.lam)

open MeasureTheory ProbabilityTheory InventoryControl in
noncomputable def p404_xi {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (X : CompoundPoissonDemand P) (θ : ℝ) (m : ℕ) (ω : Ω) : ℂ :=
  p404_ch θ (∑ l ∈ Finset.range m, (X.dem l ω : ℝ))

open MeasureTheory ProbabilityTheory InventoryControl in
noncomputable def p404_phi {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (X : CompoundPoissonDemand P) (θ : ℝ) : ℂ :=
  ∑' k : ℕ, (X.size k : ℂ) * p404_ch θ k

open MeasureTheory ProbabilityTheory InventoryControl in
noncomputable def p404_eta {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (X : CompoundPoissonDemand P) (θ : ℝ) (m : ℕ) (ω : Ω) : ℂ :=
  p404_xi X θ m ω * (p404_ch θ (X.dem m ω) - p404_phi X θ)

open MeasureTheory ProbabilityTheory InventoryControl in
noncomputable def p404_zeta {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (X : CompoundPoissonDemand P) (θ : ℝ) (m : ℕ) (ω : Ω) : ℂ :=
  ((X.gap m ω - p404_mu X : ℝ) : ℂ) * p404_xi X θ m ω

open MeasureTheory ProbabilityTheory in
lemma p404_exp_Iic (r : ℝ) (hr : 0 < r) : expMeasure r (Set.Iic 0) = 0 := by
  have := isProbabilityMeasure_expMeasure hr
  have h := cdf_expMeasure_eq hr 0
  rw [cdf_eq_real] at h
  simp only [le_refl, if_true, mul_zero, neg_zero, Real.exp_zero, sub_self] at h
  exact (measureReal_eq_zero_iff).1 h

open MeasureTheory ProbabilityTheory in
lemma p404_exp_sq (r : ℝ) (hr : 0 < r) : Integrable (fun x : ℝ => x ^ 2) (expMeasure r) := by
  have hE : expMeasure r = volume.withDensity (exponentialPDF r) := rfl
  rw [hE, integrable_withDensity_iff (f := exponentialPDF r)
    (by exact (measurable_exponentialPDFReal r).ennreal_ofReal)
    (Filter.Eventually.of_forall fun x => ENNReal.ofReal_lt_top)]
  have h := integrableOn_rpow_mul_exp_neg_mul_rpow (s := 2) (p := 1) (b := r) (by norm_num) one_pos hr
  have h2 : IntegrableOn (fun x : ℝ => r * (x ^ 2 * Real.exp (-(r * x)))) (Set.Ici 0) := by
    rw [integrableOn_Ici_iff_integrableOn_Ioi]
    refine IntegrableOn.congr_fun (h.const_mul r) (fun x _ => ?_) measurableSet_Ioi
    simp only [Real.rpow_one, neg_mul, Real.rpow_two]
  refine (h2.integrable_indicator measurableSet_Ici).congr (Filter.Eventually.of_forall fun x => ?_)
  simp only [exponentialPDF_eq]
  by_cases hx : 0 ≤ x
  · rw [Set.indicator_of_mem (show x ∈ Set.Ici 0 from hx), if_pos hx,
      ENNReal.toReal_ofReal (mul_pos hr (Real.exp_pos _)).le]
    ring
  · rw [Set.indicator_of_notMem (show x ∉ Set.Ici 0 from hx), if_neg hx]
    simp

open MeasureTheory ProbabilityTheory InventoryControl in
lemma p404_gap_pos {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (X : CompoundPoissonDemand P) : ∀ᵐ ω ∂P, ∀ n, 0 < X.gap n ω := by
  rw [ae_all_iff]
  intro n
  have h1 : P (X.gap n ⁻¹' Set.Iic 0) = 0 := by
    rw [← Measure.map_apply (X.measurable_gap n) measurableSet_Iic, X.gap_law n]
    exact p404_exp_Iic X.lam X.lam_pos
  rw [ae_iff]
  refine measure_mono_null (fun ω hω => ?_) h1
  simp only [Set.mem_setOf_eq, not_lt] at hω
  exact hω

open MeasureTheory ProbabilityTheory InventoryControl in
lemma p404_gap_memLp {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (X : CompoundPoissonDemand P) (n : ℕ) : MemLp (X.gap n) 2 P := by
  have h : MemLp (fun x : ℝ => x) 2 (P.map (X.gap n)) := by
    rw [X.gap_law n]
    haveI := isProbabilityMeasure_expMeasure X.lam_pos
    exact (memLp_two_iff_integrable_sq measurable_id.aestronglyMeasurable).2
      (p404_exp_sq X.lam X.lam_pos)
  exact (memLp_map_measure_iff measurable_id.aestronglyMeasurable
    (X.measurable_gap n).aemeasurable).1 h

open MeasureTheory ProbabilityTheory InventoryControl in
lemma p404_gap_int {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (X : CompoundPoissonDemand P) (n : ℕ) : ∫ ω, X.gap n ω ∂P = p404_mu X := by
  unfold p404_mu
  rw [← X.gap_law n, integral_map (f := fun x : ℝ => x) (X.measurable_gap n).aemeasurable
    measurable_id.aestronglyMeasurable]

open MeasureTheory ProbabilityTheory InventoryControl in
lemma p404_mu_pos {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (X : CompoundPoissonDemand P) : 0 < p404_mu X := by
  rw [← p404_gap_int X 0]
  have hint : Integrable (X.gap 0) P := (p404_gap_memLp X 0).integrable one_le_two
  have hpos : ∀ᵐ ω ∂P, 0 < X.gap 0 ω := (p404_gap_pos X).mono fun ω h => h 0
  rw [integral_pos_iff_support_of_nonneg_ae (hpos.mono fun ω h => h.le) hint, pos_iff_ne_zero]
  intro h0
  have h1 := measure_eq_zero_iff_ae_notMem.1 h0
  obtain ⟨ω, h2, h3⟩ := (hpos.and h1).exists
  exact h3 h2.ne'

open MeasureTheory ProbabilityTheory Filter Topology InventoryControl in
lemma p404_gap_slln {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (X : CompoundPoissonDemand P) :
    ∀ᵐ ω ∂P, Tendsto (fun n : ℕ => (∑ i ∈ Finset.range n, X.gap i ω) / (n : ℝ)) atTop
      (𝓝 (p404_mu X)) := by
  have h := strong_law_ae_real (μ := P) X.gap ((p404_gap_memLp X 0).integrable one_le_two)
    (fun i j hij => X.indep_gap.indepFun hij)
    (fun i => ⟨(X.measurable_gap i).aemeasurable, (X.measurable_gap 0).aemeasurable,
      by rw [X.gap_law i, X.gap_law 0]⟩)
  rw [p404_gap_int X 0] at h
  exact h

open MeasureTheory ProbabilityTheory InventoryControl in
lemma p404_dem_pos {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (X : CompoundPoissonDemand P) : ∀ᵐ ω ∂P, ∀ n, 1 ≤ X.dem n ω := by
  rw [ae_all_iff]; intro n
  have h0 : P {ω | X.dem n ω = 0} = 0 := by
    have := X.dem_law n 0
    rw [X.size_zero, measureReal_eq_zero_iff] at this
    exact this
  rw [ae_iff]
  refine measure_mono_null (fun ω hω => ?_) h0
  simp only [Set.mem_setOf_eq, not_le, Nat.lt_one_iff] at hω ⊢
  exact hω

open MeasureTheory ProbabilityTheory InventoryControl in
lemma p404_dem_integral {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (X : CompoundPoissonDemand P) (n : ℕ) (g : ℕ → ℂ) (hg : ∀ k, ‖g k‖ ≤ 1) :
    ∫ ω, g (X.dem n ω) ∂P = ∑' k, (X.size k : ℂ) * g k := by
  have hmeas : AEMeasurable (X.dem n) P := (X.measurable_dem n).aemeasurable
  rw [← integral_map hmeas (measurable_of_countable g).aestronglyMeasurable]
  haveI : IsProbabilityMeasure (P.map (X.dem n)) := Measure.isProbabilityMeasure_map hmeas
  rw [integral_countable (Integrable.of_bound (measurable_of_countable g).aestronglyMeasurable 1
    (Filter.Eventually.of_forall hg))]
  refine tsum_congr fun k => ?_
  rw [map_measureReal_apply (X.measurable_dem n) (measurableSet_singleton k), Complex.real_smul]
  congr 2
  exact X.dem_law n k

open MeasureTheory ProbabilityTheory InventoryControl in
lemma p404_dem_char {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (X : CompoundPoissonDemand P) (θ : ℝ) (m : ℕ) :
    ∫ ω, p404_ch θ (X.dem m ω : ℝ) ∂P = p404_phi X θ :=
  p404_dem_integral X m (fun k => p404_ch θ k) (fun k => (p404_ch_norm θ k).le)

lemma p404_phi_ne_one (size : ℕ → ℝ) (hnn : ∀ k, 0 ≤ size k) (hsum : HasSum size 1)
    (hap : ∀ d : ℕ, 2 ≤ d → ∃ k, 0 < size k ∧ ¬ d ∣ k) (Q r : ℕ) (hr1 : 1 ≤ r) (hrQ : r < Q) :
    ∑' k : ℕ, (size k : ℂ) * p404_ch (2 * Real.pi * r / Q) k ≠ 1 := by
  intro h
  have hs : Summable (fun k : ℕ => (size k : ℂ) * p404_ch (2 * Real.pi * r / Q) k) := by
    refine Summable.of_norm_bounded hsum.summable fun k => ?_
    rw [norm_mul, p404_ch_norm, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (hnn k)]
  have hre : ∑' k : ℕ, size k * Real.cos (2 * Real.pi * r / Q * k) = 1 := by
    have h2 := congrArg Complex.re h
    rw [Complex.re_tsum hs] at h2
    simpa only [Complex.re_ofReal_mul, p404_ch, Complex.exp_ofReal_mul_I_re, Complex.one_re]
      using h2
  have hs1 : Summable (fun k : ℕ => size k * Real.cos (2 * Real.pi * r / Q * k)) :=
    Summable.of_norm_bounded hsum.summable fun k => by
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hnn k)]
      exact mul_le_of_le_one_right (hnn k) (Real.abs_cos_le_one _)
  have hs2 : Summable (fun k : ℕ => size k * (1 - Real.cos (2 * Real.pi * r / Q * k))) :=
    (hsum.summable.sub hs1).congr fun k => by ring
  have h0 : ∑' k : ℕ, size k * (1 - Real.cos (2 * Real.pi * r / Q * k)) = 0 := by
    have e : (fun k : ℕ => size k * (1 - Real.cos (2 * Real.pi * r / Q * k)))
        = fun k => size k - size k * Real.cos (2 * Real.pi * r / Q * k) := by funext k; ring
    rw [e, Summable.tsum_sub hsum.summable hs1, hsum.tsum_eq, hre, sub_self]
  have hnn2 : ∀ k, 0 ≤ size k * (1 - Real.cos (2 * Real.pi * r / Q * k)) :=
    fun k => mul_nonneg (hnn k) (by linarith [Real.cos_le_one (2 * Real.pi * r / Q * k)])
  have hall : ∀ k, size k * (1 - Real.cos (2 * Real.pi * r / Q * k)) ≤ 0 := fun k => by
    have := hs2.le_tsum k (fun j _ => hnn2 j)
    rwa [h0] at this
  have hQpos : 0 < Q := lt_of_le_of_lt (Nat.zero_le r) hrQ
  have hg : 0 < Nat.gcd r Q := Nat.gcd_pos_of_pos_left Q hr1
  have hgr : Nat.gcd r Q ≤ r := Nat.le_of_dvd hr1 (Nat.gcd_dvd_left r Q)
  have hQg : Q / Nat.gcd r Q * Nat.gcd r Q = Q := Nat.div_mul_cancel (Nat.gcd_dvd_right r Q)
  have hrg : r / Nat.gcd r Q * Nat.gcd r Q = r := Nat.div_mul_cancel (Nat.gcd_dvd_left r Q)
  have hd : 2 ≤ Q / Nat.gcd r Q := by
    by_contra hcon
    have h1 : Q / Nat.gcd r Q ≤ 1 := by omega
    have : Q / Nat.gcd r Q * Nat.gcd r Q ≤ 1 * Nat.gcd r Q := Nat.mul_le_mul_right _ h1
    omega
  obtain ⟨k, hk, hndvd⟩ := hap (Q / Nat.gcd r Q) hd
  have hcos : Real.cos (2 * Real.pi * r / Q * k) = 1 := by
    have h1 := hall k
    have h2 : 1 - Real.cos (2 * Real.pi * r / Q * k) ≤ 0 := by
      by_contra hc; push_neg at hc
      linarith [mul_pos hk hc]
    linarith [Real.cos_le_one (2 * Real.pi * r / Q * k)]
  obtain ⟨z, hz⟩ := (Real.cos_eq_one_iff _).1 hcos
  have hQne : (Q : ℝ) ≠ 0 := by exact_mod_cast hQpos.ne'
  have e1 : 2 * Real.pi * r / Q * k * Q = 2 * Real.pi * (r * k) := by
    rw [div_mul_eq_mul_div, div_mul_cancel₀ _ hQne]; ring
  have hzQ : (z : ℝ) * Q = r * k := by
    have e2 : 2 * Real.pi * ((z : ℝ) * Q) = 2 * Real.pi * (r * k) := by
      rw [← e1, ← hz]; ring
    exact mul_left_cancel₀ (by positivity) e2
  have hdvd : Q ∣ r * k := by
    have h3 : ((r * k : ℕ) : ℤ) = z * Q := by
      have : ((r * k : ℕ) : ℝ) = ((z * Q : ℤ) : ℝ) := by push_cast; linarith
      exact_mod_cast this
    exact Int.natCast_dvd_natCast.1 ⟨z, by rw [h3]; ring⟩
  have hd' : Q / Nat.gcd r Q ∣ r / Nat.gcd r Q * k := by
    have h1 : Q / Nat.gcd r Q * Nat.gcd r Q ∣ r / Nat.gcd r Q * k * Nat.gcd r Q := by
      rw [hQg, mul_right_comm, hrg]; exact hdvd
    exact Nat.dvd_of_mul_dvd_mul_right hg h1
  have hcop : Nat.Coprime (Q / Nat.gcd r Q) (r / Nat.gcd r Q) :=
    (Nat.coprime_div_gcd_div_gcd hg).symm
  exact hndvd (hcop.dvd_of_dvd_mul_left hd')

open MeasureTheory ProbabilityTheory InventoryControl in
lemma p404_indep_prefix {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (X : CompoundPoissonDemand P) (n : ℕ) (H : (ℕ → ℕ) → ℂ)
    (hH : ∀ d d' : ℕ → ℕ, (∀ l < n, d l = d' l) → H d = H d') (G : ℕ → ℂ) :
    ∫ ω, H (fun l => X.dem l ω) * G (X.dem n ω) ∂P
      = (∫ ω, H (fun l => X.dem l ω) ∂P) * ∫ ω, G (X.dem n ω) ∂P := by
  have hind := X.indep_dem.indepFun_finset (Finset.range n) {n}
    (Finset.disjoint_singleton_right.2 (by simp)) X.measurable_dem
  let ext : (Finset.range n → ℕ) → (ℕ → ℕ) := fun v l =>
    if h : l ∈ Finset.range n then v ⟨l, h⟩ else 0
  have hHe : ∀ ω, H (ext (fun i => X.dem i ω)) = H (fun l => X.dem l ω) := fun ω =>
    hH _ _ (fun l hl => by simp only [ext]; rw [dif_pos (Finset.mem_range.2 hl)])
  have h1 := hind.integral_fun_comp_mul_comp (f := fun v => H (ext v))
    (g := fun w => G (w ⟨n, Finset.mem_singleton_self n⟩))
    (measurable_pi_lambda (fun a (i : Finset.range n) => X.dem i a)
      fun i => X.measurable_dem i).aemeasurable
    (measurable_pi_lambda (fun a (i : ({n} : Finset ℕ)) => X.dem i a)
      fun i => X.measurable_dem i).aemeasurable
    (measurable_of_countable _).aestronglyMeasurable (measurable_of_countable _).aestronglyMeasurable
  simp only [hHe] at h1
  exact h1

open MeasureTheory ProbabilityTheory InventoryControl in
lemma p404_indep_gd {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (X : CompoundPoissonDemand P) (A : (ℕ → ℝ) → ℂ) (hA : Measurable A)
    (B : (ℕ → ℕ) → ℂ) (hB : Measurable B) :
    ∫ ω, A (fun l => X.gap l ω) * B (fun l => X.dem l ω) ∂P
      = (∫ ω, A (fun l => X.gap l ω) ∂P) * ∫ ω, B (fun l => X.dem l ω) ∂P :=
  X.indep_gap_dem.integral_fun_comp_mul_comp
    (measurable_pi_lambda _ X.measurable_gap).aemeasurable
    (measurable_pi_lambda _ X.measurable_dem).aemeasurable
    hA.aestronglyMeasurable hB.aestronglyMeasurable

-- ============ Part C: character averages ============

open MeasureTheory ProbabilityTheory InventoryControl in
lemma p404_xi_norm {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (X : CompoundPoissonDemand P) (θ : ℝ) (m : ℕ) (ω : Ω) : ‖p404_xi X θ m ω‖ = 1 := by
  unfold p404_xi; exact p404_ch_norm _ _

open MeasureTheory ProbabilityTheory InventoryControl in
lemma p404_xi_succ {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (X : CompoundPoissonDemand P) (θ : ℝ) (m : ℕ) (ω : Ω) :
    p404_xi X θ (m + 1) ω = p404_xi X θ m ω * p404_ch θ (X.dem m ω) := by
  unfold p404_xi; rw [Finset.sum_range_succ, p404_ch_add]

open MeasureTheory ProbabilityTheory InventoryControl in
lemma p404_xi_meas {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (X : CompoundPoissonDemand P) (θ : ℝ) (m : ℕ) : Measurable (p404_xi X θ m) :=
  (p404_ch_meas θ).comp (Finset.measurable_sum _ fun l _ =>
    (measurable_of_countable (Nat.cast : ℕ → ℝ)).comp (X.measurable_dem l))

open MeasureTheory ProbabilityTheory InventoryControl in
lemma p404_ch_dem_meas {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (X : CompoundPoissonDemand P) (θ : ℝ) (m : ℕ) :
    Measurable (fun ω => p404_ch θ (X.dem m ω : ℝ)) :=
  (p404_ch_meas θ).comp ((measurable_of_countable (Nat.cast : ℕ → ℝ)).comp (X.measurable_dem m))

open MeasureTheory ProbabilityTheory InventoryControl in
lemma p404_phi_norm {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (X : CompoundPoissonDemand P) (θ : ℝ) : ‖p404_phi X θ‖ ≤ 1 := by
  unfold p404_phi
  have hn : ∀ k : ℕ, ‖(X.size k : ℂ) * p404_ch θ k‖ = X.size k := fun k => by
    rw [norm_mul, p404_ch_norm, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (X.size_nonneg k)]
  have hs : Summable (fun k : ℕ => ‖(X.size k : ℂ) * p404_ch θ k‖) :=
    X.size_hasSum.summable.congr fun k => (hn k).symm
  refine (norm_tsum_le_tsum_norm hs).trans (le_of_eq ?_)
  rw [tsum_congr hn, X.size_hasSum.tsum_eq]

open MeasureTheory ProbabilityTheory InventoryControl in
lemma p404_eta_meas {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (X : CompoundPoissonDemand P) (θ : ℝ) (m : ℕ) : Measurable (p404_eta X θ m) :=
  (p404_xi_meas X θ m).mul ((p404_ch_dem_meas X θ m).sub_const _)

open MeasureTheory ProbabilityTheory InventoryControl in
lemma p404_eta_le {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (X : CompoundPoissonDemand P) (θ : ℝ) (m : ℕ) (ω : Ω) : ‖p404_eta X θ m ω‖ ≤ 2 := by
  unfold p404_eta
  rw [norm_mul, p404_xi_norm, one_mul]
  calc ‖p404_ch θ (X.dem m ω) - p404_phi X θ‖
      ≤ ‖p404_ch θ (X.dem m ω)‖ + ‖p404_phi X θ‖ := norm_sub_le _ _
    _ ≤ 1 + 1 := by rw [p404_ch_norm]; linarith [p404_phi_norm X θ]
    _ = 2 := by norm_num

open MeasureTheory ProbabilityTheory InventoryControl in
lemma p404_eta_sq {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (X : CompoundPoissonDemand P) (θ : ℝ) (m : ℕ) :
    Integrable (fun ω => ‖p404_eta X θ m ω‖ ^ 2) P :=
  Integrable.of_bound ((p404_eta_meas X θ m).norm.pow_const 2).aestronglyMeasurable 4
    (Filter.Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      nlinarith [p404_eta_le X θ m ω, norm_nonneg (p404_eta X θ m ω)])

open MeasureTheory ProbabilityTheory InventoryControl in
lemma p404_eta_C {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (X : CompoundPoissonDemand P) (θ : ℝ) (m : ℕ) :
    ∫ ω, ‖p404_eta X θ m ω‖ ^ 2 ∂P ≤ 4 := by
  calc ∫ ω, ‖p404_eta X θ m ω‖ ^ 2 ∂P ≤ ∫ ω, (4:ℝ) ∂P :=
        integral_mono (p404_eta_sq X θ m) (integrable_const _) fun ω => by
          nlinarith [p404_eta_le X θ m ω, norm_nonneg (p404_eta X θ m ω)]
    _ = 4 := by simp

open MeasureTheory ProbabilityTheory InventoryControl in
lemma p404_eta_orth {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (X : CompoundPoissonDemand P) (θ : ℝ) (m m' : ℕ) (hmm : m < m') :
    ∫ ω, p404_eta X θ m ω * (starRingEnd ℂ) (p404_eta X θ m' ω) ∂P = 0 := by
  let H : (ℕ → ℕ) → ℂ := fun d => p404_ch θ (∑ l ∈ Finset.range m, (d l : ℝ))
      * (p404_ch θ (d m) - p404_phi X θ)
      * (starRingEnd ℂ) (p404_ch θ (∑ l ∈ Finset.range m', (d l : ℝ)))
  let G : ℕ → ℂ := fun k => (starRingEnd ℂ) (p404_ch θ k - p404_phi X θ)
  have hH : ∀ d d' : ℕ → ℕ, (∀ l < m', d l = d' l) → H d = H d' := by
    intro d d' hdd
    have e1 : ∑ l ∈ Finset.range m, (d l : ℝ) = ∑ l ∈ Finset.range m, (d' l : ℝ) :=
      Finset.sum_congr rfl fun l hl => by rw [hdd l ((Finset.mem_range.1 hl).trans hmm)]
    have e2 : ∑ l ∈ Finset.range m', (d l : ℝ) = ∑ l ∈ Finset.range m', (d' l : ℝ) :=
      Finset.sum_congr rfl fun l hl => by rw [hdd l (Finset.mem_range.1 hl)]
    simp only [H, e1, e2, hdd m hmm]
  have hpt : ∀ ω, p404_eta X θ m ω * (starRingEnd ℂ) (p404_eta X θ m' ω)
      = H (fun l => X.dem l ω) * G (X.dem m' ω) := by
    intro ω
    simp only [p404_eta, p404_xi, H, G, map_mul]
    ring
  simp_rw [hpt]
  rw [p404_indep_prefix X m' H hH G]
  have hint : Integrable (fun ω => p404_ch θ (X.dem m' ω : ℝ)) P :=
    Integrable.of_bound (p404_ch_dem_meas X θ m').aestronglyMeasurable 1
      (Filter.Eventually.of_forall fun ω => (p404_ch_norm _ _).le)
  have hG : ∫ ω, G (X.dem m' ω) ∂P = 0 := by
    simp only [G]
    rw [integral_conj, integral_sub hint (integrable_const _), p404_dem_char X θ m', integral_const]
    simp
  rw [hG, mul_zero]

open MeasureTheory ProbabilityTheory InventoryControl in
lemma p404_zeta_norm {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (X : CompoundPoissonDemand P) (θ : ℝ) (m : ℕ) (ω : Ω) :
    ‖p404_zeta X θ m ω‖ = |X.gap m ω - p404_mu X| := by
  unfold p404_zeta
  rw [norm_mul, p404_xi_norm, mul_one, Complex.norm_real, Real.norm_eq_abs]

open MeasureTheory ProbabilityTheory InventoryControl in
lemma p404_zeta_meas {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (X : CompoundPoissonDemand P) (θ : ℝ) (m : ℕ) : Measurable (p404_zeta X θ m) :=
  (Complex.measurable_ofReal.comp ((X.measurable_gap m).sub_const _)).mul (p404_xi_meas X θ m)

open MeasureTheory ProbabilityTheory InventoryControl in
lemma p404_zeta_sq {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (X : CompoundPoissonDemand P) (θ : ℝ) (m : ℕ) :
    Integrable (fun ω => ‖p404_zeta X θ m ω‖ ^ 2) P := by
  have h := (memLp_two_iff_integrable_sq
    (((X.measurable_gap m).sub_const (p404_mu X)).aestronglyMeasurable)).1
    ((p404_gap_memLp X m).sub (memLp_const (p404_mu X)))
  refine h.congr (Filter.Eventually.of_forall fun ω => ?_)
  simp only [p404_zeta_norm, sq_abs]

open MeasureTheory ProbabilityTheory InventoryControl in
lemma p404_zeta_C {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (X : CompoundPoissonDemand P) (θ : ℝ) (m : ℕ) :
    ∫ ω, ‖p404_zeta X θ m ω‖ ^ 2 ∂P = ∫ x, (x - p404_mu X) ^ 2 ∂(expMeasure X.lam) := by
  simp only [p404_zeta_norm, sq_abs]
  rw [← X.gap_law m, integral_map (f := fun x : ℝ => (x - p404_mu X) ^ 2)
    (X.measurable_gap m).aemeasurable ((measurable_id.sub_const _).pow_const 2).aestronglyMeasurable]

open MeasureTheory ProbabilityTheory InventoryControl in
lemma p404_zeta_orth {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (X : CompoundPoissonDemand P) (θ : ℝ) (m m' : ℕ) (hmm : m < m') :
    ∫ ω, p404_zeta X θ m ω * (starRingEnd ℂ) (p404_zeta X θ m' ω) ∂P = 0 := by
  let A : (ℕ → ℝ) → ℂ := fun g => (((g m - p404_mu X) * (g m' - p404_mu X) : ℝ) : ℂ)
  let B : (ℕ → ℕ) → ℂ := fun d => p404_ch θ (∑ l ∈ Finset.range m, (d l : ℝ))
      * (starRingEnd ℂ) (p404_ch θ (∑ l ∈ Finset.range m', (d l : ℝ)))
  have hA : Measurable A := Complex.measurable_ofReal.comp
    (((measurable_pi_apply m).sub_const _).mul ((measurable_pi_apply m').sub_const _))
  have hB : Measurable B := by
    have h1 : ∀ n, Measurable (fun d : ℕ → ℕ => ∑ l ∈ Finset.range n, (d l : ℝ)) := fun n =>
      Finset.measurable_sum _ fun l _ =>
        (measurable_of_countable (Nat.cast : ℕ → ℝ)).comp (measurable_pi_apply l)
    exact ((p404_ch_meas θ).comp (h1 m)).mul
      (Complex.continuous_conj.measurable.comp ((p404_ch_meas θ).comp (h1 m')))
  have hpt : ∀ ω, p404_zeta X θ m ω * (starRingEnd ℂ) (p404_zeta X θ m' ω)
      = A (fun l => X.gap l ω) * B (fun l => X.dem l ω) := by
    intro ω
    simp only [p404_zeta, p404_xi, A, B, map_mul, Complex.conj_ofReal]
    push_cast; ring
  simp_rw [hpt]
  rw [p404_indep_gd X A hA B hB]
  have hA0 : ∫ ω, A (fun l => X.gap l ω) ∂P = 0 := by
    simp only [A]
    rw [integral_complex_ofReal]
    have hind := (X.indep_gap.indepFun hmm.ne).integral_fun_comp_mul_comp
      (f := fun x : ℝ => x - p404_mu X) (g := fun x : ℝ => x - p404_mu X)
      (X.measurable_gap m).aemeasurable (X.measurable_gap m').aemeasurable
      (measurable_id.sub_const _).aestronglyMeasurable (measurable_id.sub_const _).aestronglyMeasurable
    rw [hind, integral_sub ((p404_gap_memLp X m).integrable one_le_two) (integrable_const _),
      p404_gap_int, integral_const]
    simp
  rw [hA0, zero_mul]

open MeasureTheory ProbabilityTheory Filter Topology InventoryControl in
lemma p404_zeta_b {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (X : CompoundPoissonDemand P) (θ : ℝ) :
    ∀ᵐ ω ∂P, (∀ m, ‖p404_zeta X θ m ω‖ ≤ |X.gap m ω| + p404_mu X) ∧
      Tendsto (fun n : ℕ => (∑ m ∈ Finset.range n, (|X.gap m ω| + p404_mu X)) / (n : ℝ)) atTop
        (𝓝 (p404_mu X + p404_mu X)) := by
  filter_upwards [p404_gap_slln X, p404_gap_pos X] with ω h1 h2
  refine ⟨fun m => ?_, ?_⟩
  · rw [p404_zeta_norm]
    exact abs_le.2 ⟨by linarith [neg_abs_le (X.gap m ω), p404_mu_pos X],
      by linarith [le_abs_self (X.gap m ω), p404_mu_pos X]⟩
  · have h3 := h1.add_const (p404_mu X)
    refine h3.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
    have h2' : ∀ m, |X.gap m ω| = X.gap m ω := fun m => abs_of_pos (h2 m)
    simp only [h2', Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    rw [add_div, mul_div_cancel_left₀ _ hn']

open MeasureTheory ProbabilityTheory Filter Topology InventoryControl in
lemma p404_char_avg {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (X : CompoundPoissonDemand P) (θ : ℝ) (hφ : p404_phi X θ ≠ 1) :
    ∀ᵐ ω ∂P, Tendsto (fun n : ℕ => (∑ m ∈ Finset.range n, (X.gap m ω : ℂ) * p404_xi X θ m ω)
      / (n : ℂ)) atTop (𝓝 0) := by
  have hη := p404_slln_orth (p404_eta X θ) 4 (p404_eta_meas X θ) (p404_eta_sq X θ)
    (p404_eta_C X θ) (p404_eta_orth X θ) (fun _ _ => (2:ℝ)) (fun _ => (2:ℝ))
    (Filter.Eventually.of_forall fun ω => ⟨fun m => p404_eta_le X θ m ω, p404_const_avg 2⟩)
  have hζ := p404_slln_orth (p404_zeta X θ) (∫ x, (x - p404_mu X) ^ 2 ∂(expMeasure X.lam))
    (p404_zeta_meas X θ) (p404_zeta_sq X θ) (fun m => (p404_zeta_C X θ m).le)
    (p404_zeta_orth X θ) (fun m ω => |X.gap m ω| + p404_mu X) (fun _ => p404_mu X + p404_mu X)
    (p404_zeta_b X θ)
  filter_upwards [hη, hζ] with ω h1 h2
  have h1φ : (1 - p404_phi X θ) ≠ 0 := sub_ne_zero.2 (Ne.symm hφ)
  have hid : ∀ n : ℕ, ∑ m ∈ Finset.range n, (X.gap m ω : ℂ) * p404_xi X θ m ω
      = (p404_mu X : ℂ) / (1 - p404_phi X θ) * ((∑ m ∈ Finset.range n, p404_eta X θ m ω)
          - p404_xi X θ n ω + p404_xi X θ 0 ω)
        + ∑ m ∈ Finset.range n, p404_zeta X θ m ω := by
    intro n
    have hη' : ∑ m ∈ Finset.range n, p404_eta X θ m ω
        = (p404_xi X θ n ω - p404_xi X θ 0 ω)
          + (1 - p404_phi X θ) * ∑ m ∈ Finset.range n, p404_xi X θ m ω := by
      rw [← Finset.sum_range_sub (fun m => p404_xi X θ m ω), Finset.mul_sum,
        ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun m _ => ?_
      simp only [p404_eta, p404_xi_succ]
      ring
    have hζ' : ∑ m ∈ Finset.range n, p404_zeta X θ m ω
        = ∑ m ∈ Finset.range n, (X.gap m ω : ℂ) * p404_xi X θ m ω
          - (p404_mu X : ℂ) * ∑ m ∈ Finset.range n, p404_xi X θ m ω := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun m _ => ?_
      simp only [p404_zeta]; push_cast; ring
    rw [hζ', hη']
    have e : p404_xi X θ n ω - p404_xi X θ 0 ω
        + (1 - p404_phi X θ) * ∑ m ∈ Finset.range n, p404_xi X θ m ω
        - p404_xi X θ n ω + p404_xi X θ 0 ω
        = (1 - p404_phi X θ) * ∑ m ∈ Finset.range n, p404_xi X θ m ω := by ring
    rw [e, ← mul_assoc, div_mul_cancel₀ _ h1φ]
    ring
  have hxn : Tendsto (fun n : ℕ => p404_xi X θ n ω / (n : ℂ)) atTop (𝓝 0) := by
    refine squeeze_zero_norm (fun n => ?_) (tendsto_const_div_atTop_nhds_zero_nat (1:ℝ))
    rw [norm_div, p404_xi_norm, Complex.norm_natCast]
  have hx0 : Tendsto (fun n : ℕ => p404_xi X θ 0 ω / (n : ℂ)) atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat _
  have hlim := (((h1.sub hxn).add hx0).const_mul ((p404_mu X : ℂ) / (1 - p404_phi X θ))).add h2
  simp only [sub_zero, add_zero, mul_zero] at hlim
  refine hlim.congr fun n => ?_
  rw [hid n]; ring

lemma p404_fourier (Q : ℕ) (hQ : 0 < Q) (y : ℤ) :
    ∑ r ∈ Finset.range Q, p404_ch (2 * Real.pi * r / Q) (y : ℝ)
      = if (Q : ℤ) ∣ y then (Q : ℂ) else 0 := by
  have hprim := Complex.isPrimitiveRoot_exp Q hQ.ne'
  set ζ := Complex.exp (2 * ↑Real.pi * Complex.I / ↑Q) with hζ
  have hw : ∀ r : ℕ, p404_ch (2 * Real.pi * r / Q) (y : ℝ) = (ζ ^ y) ^ r := by
    intro r
    rw [hζ, ← Complex.exp_int_mul, ← Complex.exp_nat_mul, p404_ch]
    congr 1; push_cast; ring
  simp_rw [hw]
  split_ifs with h
  · rw [(hprim.zpow_eq_one_iff_dvd y).2 h]; simp
  · have hne : ζ ^ y ≠ 1 := fun h' => h ((hprim.zpow_eq_one_iff_dvd y).1 h')
    rw [geom_sum_eq hne]
    have : (ζ ^ y) ^ Q = 1 := by
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hprim.pow_eq_one, one_zpow]
    rw [this, sub_self, zero_div]

open InventoryControl in
lemma p404_band_iff (R : ℤ) (Q : ℕ) (hQ : 0 < Q) (j : ℤ) (hj1 : R + 1 ≤ j) (hj2 : j ≤ R + Q)
    (y0 S : ℤ) : reduceToBand R Q (y0 - S) = j ↔ (Q : ℤ) ∣ S + (j - y0) := by
  have hQ' : (0 : ℤ) < Q := by exact_mod_cast hQ
  have hjm : (j - (R + 1)) % (Q : ℤ) = j - (R + 1) :=
    Int.emod_eq_of_lt (by linarith) (by linarith)
  unfold reduceToBand
  constructor
  · intro h
    have h1 : (y0 - S - (R + 1)) % (Q : ℤ) = (j - (R + 1)) % (Q : ℤ) := by rw [hjm]; linarith
    have h2 := (Int.ModEq.dvd h1)
    have e : S + (j - y0) = (j - (R + 1)) - (y0 - S - (R + 1)) := by ring
    rw [e]; exact h2
  · intro h
    have e : S + (j - y0) = (j - (R + 1)) - (y0 - S - (R + 1)) := by ring
    rw [e] at h
    have h1 : (y0 - S - (R + 1)) % (Q : ℤ) = (j - (R + 1)) % (Q : ℤ) :=
      (Int.modEq_iff_dvd.2 h)
    rw [h1, hjm]; ring

-- ============ Part D: pathwise conversion and assembly ============

open Filter Topology Finset in
lemma p404_ctime (g f : ℕ → ℝ) (μ L : ℝ) (hμ : 0 < μ)
    (hg : ∀ n, 0 < g n) (hf0 : ∀ n, 0 ≤ f n) (hf1 : ∀ n, f n ≤ 1)
    (hG : Tendsto (fun n : ℕ => (∑ m ∈ range n, g m) / (n : ℝ)) atTop (𝓝 μ))
    (hF : Tendsto (fun n : ℕ => (∑ m ∈ range n, g m * f m) / (n : ℝ)) atTop (𝓝 (μ * L)))
    (N : ℝ → ℕ)
    (hN : ∀ T, 0 ≤ T → (∑ m ∈ range (N T), g m) ≤ T ∧ T < ∑ m ∈ range (N T + 1), g m)
    (I : ℝ → ℝ)
    (hI : ∀ T, 0 ≤ T →
      I T = ∑ m ∈ range (N T), g m * f m + (T - ∑ m ∈ range (N T), g m) * f (N T)) :
    Tendsto (fun T => (1 / T) * I T) atTop (𝓝 L) := by
  have hmono : ∀ a b, a ≤ b → ∑ m ∈ range a, g m ≤ ∑ m ∈ range b, g m := fun a b hab =>
    sum_le_sum_of_subset_of_nonneg (range_mono hab) (fun m _ _ => (hg m).le)
  have hNt : Tendsto N atTop atTop := by
    refine tendsto_atTop_atTop.2 fun K => ⟨∑ m ∈ range K, g m, fun T hT => ?_⟩
    have hT0 : 0 ≤ T := le_trans (sum_nonneg fun m _ => (hg m).le) hT
    by_contra hlt
    push_neg at hlt
    have h1 := (hN T hT0).2
    have h2 := hmono (N T + 1) K hlt
    linarith
  have hratio : Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ) / (n : ℝ)) atTop (𝓝 1) := by
    have h3 : Tendsto (fun n : ℕ => 1 + 1 / (n : ℝ)) atTop (𝓝 (1 + 0)) :=
      tendsto_const_nhds.add tendsto_one_div_atTop_nhds_zero_nat
    rw [add_zero] at h3
    refine h3.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
    rw [Nat.cast_add, Nat.cast_one, add_div, div_self hn']
  have hA1 : Tendsto (fun n : ℕ => (∑ m ∈ range (n + 1), g m) / (n : ℝ)) atTop (𝓝 μ) := by
    have h4 := (hG.comp (tendsto_add_atTop_nat 1)).mul hratio
    rw [mul_one] at h4
    refine h4.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hn1 : ((n + 1 : ℕ) : ℝ) ≠ 0 := by positivity
    simp only [Function.comp]
    rw [div_mul_div_cancel₀ hn1]
  have hTN : Tendsto (fun T : ℝ => T / (N T : ℝ)) atTop (𝓝 μ) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' (hG.comp hNt) (hA1.comp hNt) ?_ ?_
    · filter_upwards [eventually_ge_atTop (0:ℝ)] with T hT
      exact div_le_div_of_nonneg_right (hN T hT).1 (Nat.cast_nonneg _)
    · filter_upwards [eventually_ge_atTop (0:ℝ)] with T hT
      exact div_le_div_of_nonneg_right (hN T hT).2.le (Nat.cast_nonneg _)
  have hNT : Tendsto (fun T : ℝ => (N T : ℝ) / T) atTop (𝓝 μ⁻¹) := by
    refine (hTN.inv₀ hμ.ne').congr fun T => ?_
    rw [inv_div]
  have hmain := (hF.comp hNt).mul hNT
  have hrem : Tendsto (fun T : ℝ => (T - ∑ m ∈ range (N T), g m) / T * f (N T)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun T : ℝ => 1 - (∑ m ∈ range (N T), g m) / (N T : ℝ) * ((N T : ℝ) / T))
        atTop (𝓝 (1 - μ * μ⁻¹)) := tendsto_const_nhds.sub ((hG.comp hNt).mul hNT)
    rw [mul_inv_cancel₀ hμ.ne', sub_self] at h1
    refine squeeze_zero_norm' ?_ h1
    filter_upwards [eventually_gt_atTop (0:ℝ), hNt.eventually_ge_atTop 1] with T hT hN1
    have hNne : (N T : ℝ) ≠ 0 := by exact_mod_cast (show N T ≠ 0 by omega)
    have hT' : T ≠ 0 := hT.ne'
    have hA := (hN T hT.le).1
    have e : 1 - (∑ m ∈ range (N T), g m) / (N T : ℝ) * ((N T : ℝ) / T)
        = (T - ∑ m ∈ range (N T), g m) / T := by
      field_simp
      try ring
    rw [e, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (hf0 _),
      abs_of_nonneg (div_nonneg (by linarith) hT.le)]
    exact mul_le_of_le_one_right (div_nonneg (by linarith) hT.le) (hf1 _)
  have hsum := hmain.add hrem
  have hlim : μ * L * μ⁻¹ + 0 = L := by
    rw [add_zero, mul_comm μ L, mul_assoc, mul_inv_cancel₀ hμ.ne', mul_one]
  rw [hlim] at hsum
  refine hsum.congr' ?_
  filter_upwards [eventually_gt_atTop (0:ℝ), hNt.eventually_ge_atTop 1] with T hT hN1
  have hNne : (N T : ℝ) ≠ 0 := by exact_mod_cast (show N T ≠ 0 by omega)
  have hT' : T ≠ 0 := hT.ne'
  simp only [Function.comp]
  rw [hI T hT.le]
  field_simp
  try ring

open InventoryControl in
lemma p404_arr_mono {Ω : Type*} [MeasurableSpace Ω] {P : MeasureTheory.Measure Ω}
    (X : CompoundPoissonDemand P) (ω : Ω) (hg : ∀ n, 0 < X.gap n ω) (a b : ℕ) (hab : a ≤ b) :
    X.arrival a ω ≤ X.arrival b ω := by
  unfold CompoundPoissonDemand.arrival
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hab) (fun i _ _ => (hg i).le)

open Filter Topology InventoryControl in
lemma p404_arr_tendsto {Ω : Type*} [MeasurableSpace Ω] {P : MeasureTheory.Measure Ω}
    (X : CompoundPoissonDemand P) (ω : Ω) (μ : ℝ) (hμ : 0 < μ)
    (hG : Tendsto (fun n : ℕ => (∑ i ∈ Finset.range n, X.gap i ω) / (n : ℝ)) atTop (𝓝 μ)) :
    Tendsto (fun n => X.arrival n ω) atTop atTop := by
  have h := Filter.Tendsto.pos_mul_atTop hμ hG tendsto_natCast_atTop_atTop
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  simp only [CompoundPoissonDemand.arrival]
  rw [div_mul_cancel₀ _ hn']

open InventoryControl in
lemma p404_count_eq {Ω : Type*} [MeasurableSpace Ω] {P : MeasureTheory.Measure Ω}
    (X : CompoundPoissonDemand P) (ω : Ω) (hg : ∀ n, 0 < X.gap n ω) (m : ℕ) (t : ℝ)
    (h1 : X.arrival m ω ≤ t) (h2 : t < X.arrival (m + 1) ω) : X.count t ω = m := by
  unfold CompoundPoissonDemand.count
  refine IsGreatest.csSup_eq ⟨h1, fun n hn => ?_⟩
  by_contra hlt
  push_neg at hlt
  have := p404_arr_mono X ω hg (m + 1) n hlt
  simp only [Set.mem_setOf_eq] at hn
  linarith

open Filter Topology InventoryControl in
lemma p404_count_bracket {Ω : Type*} [MeasurableSpace Ω] {P : MeasureTheory.Measure Ω}
    (X : CompoundPoissonDemand P) (ω : Ω) (hg : ∀ n, 0 < X.gap n ω)
    (hinf : Tendsto (fun n => X.arrival n ω) atTop atTop) (T : ℝ) (hT : 0 ≤ T) :
    X.arrival (X.count T ω) ω ≤ T ∧ T < X.arrival (X.count T ω + 1) ω := by
  have hex : ∃ k, T < X.arrival (k + 1) ω := by
    obtain ⟨k, hk⟩ := (hinf.eventually_gt_atTop T).exists
    exact ⟨k, lt_of_lt_of_le hk (p404_arr_mono X ω hg k (k + 1) (Nat.le_succ k))⟩
  classical
  have hk1 : T < X.arrival (Nat.find hex + 1) ω := Nat.find_spec hex
  have hk2 : X.arrival (Nat.find hex) ω ≤ T := by
    rcases Nat.eq_zero_or_pos (Nat.find hex) with h0 | hpos
    · rw [h0]; simp [CompoundPoissonDemand.arrival, hT]
    · obtain ⟨j, hj⟩ : ∃ j, Nat.find hex = j + 1 := ⟨Nat.find hex - 1, by omega⟩
      have := Nat.find_min hex (show j < Nat.find hex by omega)
      push_neg at this
      rw [hj]; exact this
  rw [p404_count_eq X ω hg (Nat.find hex) T hk2 hk1]
  exact ⟨hk2, hk1⟩

open Filter Topology InventoryControl in
lemma p404_count_mono {Ω : Type*} [MeasurableSpace Ω] {P : MeasureTheory.Measure Ω}
    (X : CompoundPoissonDemand P) (ω : Ω) (hg : ∀ n, 0 < X.gap n ω)
    (hinf : Tendsto (fun n => X.arrival n ω) atTop atTop) : Monotone (fun t => X.count t ω) := by
  intro s t hst
  unfold CompoundPoissonDemand.count
  apply csSup_le_csSup'
  · obtain ⟨K, hK⟩ := (hinf.eventually_gt_atTop t).exists
    refine ⟨K, fun n hn => ?_⟩
    by_contra hlt
    push_neg at hlt
    have := p404_arr_mono X ω hg K n hlt.le
    simp only [Set.mem_setOf_eq] at hn
    linarith
  · intro n hn
    simp only [Set.mem_setOf_eq] at hn ⊢
    linarith

open MeasureTheory Filter Topology InventoryControl in
lemma p404_integral_decomp {Ω : Type*} [MeasurableSpace Ω] {P : MeasureTheory.Measure Ω}
    (X : CompoundPoissonDemand P) (ω : Ω) (hg : ∀ n, 0 < X.gap n ω)
    (hinf : Tendsto (fun n => X.arrival n ω) atTop atTop) (f : ℕ → ℝ) (hf : ∀ n, |f n| ≤ 1)
    (T : ℝ) (hT : 0 ≤ T) :
    ∫ t in (0:ℝ)..T, f (X.count t ω) = ∑ m ∈ Finset.range (X.count T ω), X.gap m ω * f m
      + (T - X.arrival (X.count T ω) ω) * f (X.count T ω) := by
  have hmeas : Measurable (fun t => f (X.count t ω)) :=
    (measurable_of_countable f).comp (p404_count_mono X ω hg hinf).measurable
  have hII : ∀ a b : ℝ, IntervalIntegrable (fun t => f (X.count t ω)) volume a b := by
    intro a b
    refine (intervalIntegrable_const (c := (1:ℝ))).mono_fun hmeas.aestronglyMeasurable ?_
    exact Filter.Eventually.of_forall fun t => by simpa [Real.norm_eq_abs] using hf (X.count t ω)
  have harr0 : X.arrival 0 ω = 0 := by simp [CompoundPoissonDemand.arrival]
  have hpiece : ∀ k, ∫ t in (X.arrival k ω)..(X.arrival (k + 1) ω), f (X.count t ω)
      = X.gap k ω * f k := by
    intro k
    have hle : X.arrival k ω ≤ X.arrival (k + 1) ω := p404_arr_mono X ω hg k (k + 1) (Nat.le_succ k)
    rw [intervalIntegral.integral_congr_ae (g := fun _ => f k) ?_, intervalIntegral.integral_const,
      smul_eq_mul]
    · congr 1
      simp [CompoundPoissonDemand.arrival, Finset.sum_range_succ]
    · filter_upwards [Measure.ae_ne volume (X.arrival (k + 1) ω)] with t ht htI
      rw [Set.uIoc_of_le hle] at htI
      exact congrArg f (p404_count_eq X ω hg k t htI.1.le (lt_of_le_of_ne htI.2 ht))
  obtain ⟨h1, h2⟩ := p404_count_bracket X ω hg hinf T hT
  have hlast : ∫ t in (X.arrival (X.count T ω) ω)..T, f (X.count t ω)
      = (T - X.arrival (X.count T ω) ω) * f (X.count T ω) := by
    rw [intervalIntegral.integral_congr (g := fun _ => f (X.count T ω)) ?_,
      intervalIntegral.integral_const, smul_eq_mul]
    intro t ht
    rw [Set.uIcc_of_le h1] at ht
    exact congrArg f (p404_count_eq X ω hg (X.count T ω) t ht.1 (lt_of_le_of_lt ht.2 h2))
  have hsum := intervalIntegral.sum_integral_adjacent_intervals (a := fun k => X.arrival k ω)
    (n := X.count T ω) (μ := volume) (fun k _ => hII _ _)
  simp only [harr0] at hsum
  rw [← intervalIntegral.integral_add_adjacent_intervals (hII 0 (X.arrival (X.count T ω) ω))
    (hII _ T), hlast, ← hsum]
  simp only [hpiece]

lemma p404_ite01 (c : Prop) [Decidable c] :
    0 ≤ (if c then (1:ℝ) else 0) ∧ (if c then (1:ℝ) else 0) ≤ 1 ∧ |if c then (1:ℝ) else 0| ≤ 1 := by
  split_ifs <;> norm_num

open MeasureTheory ProbabilityTheory Filter Topology InventoryControl in
lemma p404_discrete {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (X : CompoundPoissonDemand P) (R : ℤ) (Q : ℕ) (hQ : 0 < Q) (y0 j : ℤ)
    (hj1 : R + 1 ≤ j) (hj2 : j ≤ R + Q) :
    ∀ᵐ ω ∂P, Tendsto (fun n : ℕ => (∑ m ∈ Finset.range n,
        X.gap m ω * (if reduceToBand R Q (y0 - (X.cumDemand m ω : ℤ)) = j then (1:ℝ) else 0))
          / (n : ℝ)) atTop
      (𝓝 (p404_mu X * (1 / (Q : ℝ)))) := by
  have hchar : ∀ᵐ ω ∂P, ∀ r : ℕ, r < Q → Tendsto (fun n : ℕ => (∑ m ∈ Finset.range n,
      (X.gap m ω : ℂ) * p404_xi X (2 * Real.pi * r / Q) m ω) / (n : ℂ)) atTop
      (𝓝 (if r = 0 then (p404_mu X : ℂ) else 0)) := by
    rw [ae_all_iff]
    intro r
    by_cases hr : r < Q
    · rcases Nat.eq_zero_or_pos r with h0 | hpos
      · subst h0
        filter_upwards [p404_gap_slln X] with ω hω _
        rw [if_pos rfl]
        have := (Complex.continuous_ofReal.tendsto _).comp hω
        refine this.congr fun n => ?_
        simp [p404_xi, p404_ch]
      · filter_upwards [p404_char_avg X _ (p404_phi_ne_one X.size X.size_nonneg X.size_hasSum
          X.size_aperiodic Q r hpos hr)] with ω hω _
        rw [if_neg hpos.ne']
        exact hω
    · exact Filter.Eventually.of_forall fun ω h => absurd h hr
  filter_upwards [hchar] with ω hω
  set κ : ℕ → ℂ := fun r => p404_ch (2 * Real.pi * r / Q) ((j - y0 : ℤ) : ℝ) with hκ
  have hQne : (Q : ℂ) ≠ 0 := by exact_mod_cast hQ.ne'
  have hind : ∀ m, 0 ≤ m →
      ((X.gap m ω * (if reduceToBand R Q (y0 - (X.cumDemand m ω : ℤ)) = j then (1:ℝ) else 0)
          : ℝ) : ℂ)
        = (1 / (Q : ℂ)) * ∑ r ∈ Finset.range Q,
            κ r * ((X.gap m ω : ℂ) * p404_xi X (2 * Real.pi * r / Q) m ω) := by
    intro m _
    have hiff := p404_band_iff R Q hQ j hj1 hj2 y0 (X.cumDemand m ω : ℤ)
    have hF := p404_fourier Q hQ ((X.cumDemand m ω : ℤ) + (j - y0))
    have hsplit : ∀ r : ℕ, p404_ch (2 * Real.pi * r / Q)
        ((((X.cumDemand m ω : ℤ) + (j - y0) : ℤ)) : ℝ)
        = κ r * p404_xi X (2 * Real.pi * r / Q) m ω := by
      intro r
      simp only [hκ, p404_xi]
      rw [mul_comm, ← p404_ch_add]
      congr 1
      unfold CompoundPoissonDemand.cumDemand
      push_cast
      ring
    have hsum : ∑ r ∈ Finset.range Q,
        κ r * ((X.gap m ω : ℂ) * p404_xi X (2 * Real.pi * r / Q) m ω)
        = (X.gap m ω : ℂ) * ∑ r ∈ Finset.range Q, p404_ch (2 * Real.pi * r / Q)
            ((((X.cumDemand m ω : ℤ) + (j - y0) : ℤ)) : ℝ) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun r _ => ?_
      rw [hsplit]; ring
    rw [hsum, hF]
    by_cases hj : reduceToBand R Q (y0 - (X.cumDemand m ω : ℤ)) = j
    · rw [if_pos hj, if_pos (hiff.1 hj)]
      push_cast
      field_simp
    · rw [if_neg hj, if_neg (fun h => hj (hiff.2 h))]
      push_cast
      ring
  have hlimC : Tendsto (fun n : ℕ => (∑ m ∈ Finset.range n, (1 / (Q : ℂ)) * ∑ r ∈ Finset.range Q,
      κ r * ((X.gap m ω : ℂ) * p404_xi X (2 * Real.pi * r / Q) m ω)) / (n : ℂ)) atTop
      (𝓝 ((p404_mu X : ℂ) * (1 / (Q : ℂ)))) := by
    have h1 : Tendsto (fun n : ℕ => (1 / (Q : ℂ)) * ∑ r ∈ Finset.range Q, κ r *
        ((∑ m ∈ Finset.range n, (X.gap m ω : ℂ) * p404_xi X (2 * Real.pi * r / Q) m ω)
          / (n : ℂ))) atTop
        (𝓝 ((1 / (Q : ℂ)) * ∑ r ∈ Finset.range Q, κ r * (if r = 0 then (p404_mu X : ℂ) else 0))) :=
      tendsto_const_nhds.mul (tendsto_finset_sum _ fun r hr =>
        tendsto_const_nhds.mul (hω r (Finset.mem_range.1 hr)))
    have hκ0 : κ 0 = 1 := by simp [hκ, p404_ch]
    have hval : (1 / (Q : ℂ)) * ∑ r ∈ Finset.range Q, κ r * (if r = 0 then (p404_mu X : ℂ) else 0)
        = (p404_mu X : ℂ) * (1 / (Q : ℂ)) := by
      rw [Finset.sum_eq_single 0 (fun b _ hb => by rw [if_neg hb, mul_zero])
        (fun h => absurd (Finset.mem_range.2 hQ) h), if_pos rfl, hκ0, one_mul, mul_comm]
    rw [hval] at h1
    refine h1.congr fun n => ?_
    simp only [Finset.mul_sum, Finset.sum_div]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun r _ => ?_
    ring
  have hC := p404_event_avg
    (fun m => ((X.gap m ω * (if reduceToBand R Q (y0 - (X.cumDemand m ω : ℤ)) = j
      then (1:ℝ) else 0) : ℝ) : ℂ)) _ 0 hind _ hlimC
  have hR := (Complex.continuous_re.tendsto _).comp hC
  have hval : ((p404_mu X : ℂ) * (1 / (Q : ℂ))).re = p404_mu X * (1 / (Q : ℝ)) := by
    rw [show (p404_mu X : ℂ) * (1 / (Q : ℂ)) = ((p404_mu X * (1 / (Q : ℝ)) : ℝ) : ℂ) by
      push_cast; ring, Complex.ofReal_re]
  rw [hval] at hR
  refine hR.congr fun n => ?_
  simp only [Function.comp]
  rw [← Complex.ofReal_natCast, ← Complex.ofReal_sum, ← Complex.ofReal_div, Complex.ofReal_re]

open MeasureTheory ProbabilityTheory Filter Topology InventoryControl in
theorem solution {Ω : Type*} [MeasurableSpace Ω] {P : MeasureTheory.Measure Ω}
    [MeasureTheory.IsProbabilityMeasure P] (X : CompoundPoissonDemand P) (R : ℤ) (Q : ℕ)
    (hQ : 0 < Q) (y0 : ℤ) (j : ℤ) (hj1 : R + 1 ≤ j) (hj2 : j ≤ R + Q) :
    ∀ᵐ ω ∂P, Filter.Tendsto
      (fun T : ℝ => (1 / T) * ∫ t in (0 : ℝ)..T,
          (if reduceToBand R Q (y0 - (X.cumDemand (X.count t ω) ω : ℤ)) = j then (1 : ℝ) else 0))
      Filter.atTop (nhds (1 / (Q : ℝ))) := by
  filter_upwards [p404_gap_pos X, p404_gap_slln X, p404_discrete X R Q hQ y0 j hj1 hj2]
    with ω hg hG hF
  have hμ := p404_mu_pos X
  have hinf := p404_arr_tendsto X ω (p404_mu X) hμ hG
  exact p404_ctime (fun n => X.gap n ω)
    (fun n => if reduceToBand R Q (y0 - (X.cumDemand n ω : ℤ)) = j then (1 : ℝ) else 0)
    (p404_mu X) (1 / (Q : ℝ)) hμ hg (fun n => (p404_ite01 _).1) (fun n => (p404_ite01 _).2.1)
    hG hF (fun T => X.count T ω) (fun T hT => p404_count_bracket X ω hg hinf T hT)
    (fun T => ∫ t in (0 : ℝ)..T,
      (if reduceToBand R Q (y0 - (X.cumDemand (X.count t ω) ω : ℤ)) = j then (1 : ℝ) else 0))
    (fun T hT => p404_integral_decomp X ω hg hinf
      (fun n => if reduceToBand R Q (y0 - (X.cumDemand n ω : ℤ)) = j then (1 : ℝ) else 0)
      (fun n => (p404_ite01 _).2.2) T hT)
