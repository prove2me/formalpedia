-- Prove2me | solution 1 for InventoryControl.rq_policy_cost
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-27T20:23:26.30279+00:00
-- url     : https://prove2.me/submissions/aca0ff50-b4fa-4088-a91c-3da0e406a4c5

import Mathlib
import Definitions.Def_InventoryControl_rqPolicy

set_option autoImplicit false

open Filter Topology in
lemma p0d2_sqrt_tendsto : Tendsto Nat.sqrt atTop atTop :=
  tendsto_atTop_atTop.2 fun b => ⟨b ^ 2, fun _ hn => Nat.le_sqrt'.2 hn⟩

open Filter Topology in
lemma p0d2_ratio : Tendsto (fun k : ℕ => (((k + 1) ^ 2 : ℕ) : ℝ) / ((k ^ 2 : ℕ) : ℝ)) atTop (𝓝 1) := by
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
lemma p0d2_interp (z : ℕ → ℂ) (b : ℕ → ℝ) (β : ℝ)
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
    have h3 := (h1.mul p0d2_ratio).sub h2
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
  refine squeeze_zero_norm' ?_ (hu.comp p0d2_sqrt_tendsto)
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
lemma p0d2_L2 {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
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
lemma p0d2_ae_sq {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (Z : ℕ → Ω → ℂ) (C : ℝ) (hmeas : ∀ m, Measurable (Z m))
    (hsq : ∀ m, Integrable (fun ω => ‖Z m ω‖ ^ 2) P)
    (hC : ∀ m, ∫ ω, ‖Z m ω‖ ^ 2 ∂P ≤ C)
    (horth : ∀ m m', m < m' → ∫ ω, Z m ω * (starRingEnd ℂ) (Z m' ω) ∂P = 0) :
    ∀ᵐ ω ∂P, Tendsto (fun k : ℕ => (∑ m ∈ range (k ^ 2), Z m ω) / ((k ^ 2 : ℕ) : ℂ))
      atTop (𝓝 0) := by
  have hL2 := p0d2_L2 Z C hmeas hsq hC horth
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
lemma p0d2_slln_orth {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (Z : ℕ → Ω → ℂ) (C : ℝ) (hmeas : ∀ m, Measurable (Z m))
    (hsq : ∀ m, Integrable (fun ω => ‖Z m ω‖ ^ 2) P)
    (hC : ∀ m, ∫ ω, ‖Z m ω‖ ^ 2 ∂P ≤ C)
    (horth : ∀ m m', m < m' → ∫ ω, Z m ω * (starRingEnd ℂ) (Z m' ω) ∂P = 0)
    (b : ℕ → Ω → ℝ) (β : Ω → ℝ)
    (hb : ∀ᵐ ω ∂P, (∀ m, ‖Z m ω‖ ≤ b m ω) ∧
      Tendsto (fun n : ℕ => (∑ m ∈ range n, b m ω) / (n : ℝ)) atTop (𝓝 (β ω))) :
    ∀ᵐ ω ∂P, Tendsto (fun n : ℕ => (∑ m ∈ range n, Z m ω) / (n : ℂ)) atTop (𝓝 0) := by
  filter_upwards [p0d2_ae_sq Z C hmeas hsq hC horth, hb] with ω h1 h2
  exact p0d2_interp (fun m => Z m ω) (fun m => b m ω) (β ω) h2.1 h2.2 h1

open Filter Topology Finset in
lemma p0d2_const_avg (c : ℝ) :
    Tendsto (fun n : ℕ => (∑ m ∈ range n, c) / (n : ℝ)) atTop (𝓝 c) := by
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_div_cancel_left₀ _ hn']

open Filter Topology Finset in
lemma p0d2_event_avg (a b : ℕ → ℂ) (n0 : ℕ) (hab : ∀ m, n0 ≤ m → a m = b m) (L : ℂ)
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

noncomputable def p0d2_ch (θ x : ℝ) : ℂ := Complex.exp (↑(θ * x) * Complex.I)

lemma p0d2_ch_norm (θ x : ℝ) : ‖p0d2_ch θ x‖ = 1 := Complex.norm_exp_ofReal_mul_I _

lemma p0d2_ch_add (θ x y : ℝ) : p0d2_ch θ (x + y) = p0d2_ch θ x * p0d2_ch θ y := by
  unfold p0d2_ch
  rw [← Complex.exp_add]; congr 1; push_cast; ring

lemma p0d2_ch_zero (θ : ℝ) : p0d2_ch θ 0 = 1 := by simp [p0d2_ch]

lemma p0d2_ch_meas (θ : ℝ) : Measurable (fun x => p0d2_ch θ x) :=
  (by unfold p0d2_ch; fun_prop : Continuous (fun x => p0d2_ch θ x)).measurable

open MeasureTheory ProbabilityTheory InventoryControl in
noncomputable def p0d2_mu {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (X : CompoundPoissonDemand P) : ℝ :=
  ∫ x, x ∂(expMeasure X.lam)

open MeasureTheory ProbabilityTheory InventoryControl in
noncomputable def p0d2_xi {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (X : CompoundPoissonDemand P) (θ : ℝ) (m : ℕ) (ω : Ω) : ℂ :=
  p0d2_ch θ (∑ l ∈ Finset.range m, (X.dem l ω : ℝ))

open MeasureTheory ProbabilityTheory InventoryControl in
noncomputable def p0d2_phi {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (X : CompoundPoissonDemand P) (θ : ℝ) : ℂ :=
  ∑' k : ℕ, (X.size k : ℂ) * p0d2_ch θ k

open MeasureTheory ProbabilityTheory InventoryControl in
noncomputable def p0d2_eta {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (X : CompoundPoissonDemand P) (θ : ℝ) (m : ℕ) (ω : Ω) : ℂ :=
  p0d2_xi X θ m ω * (p0d2_ch θ (X.dem m ω) - p0d2_phi X θ)

open MeasureTheory ProbabilityTheory InventoryControl in
noncomputable def p0d2_zeta {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (X : CompoundPoissonDemand P) (θ : ℝ) (m : ℕ) (ω : Ω) : ℂ :=
  ((X.gap m ω - p0d2_mu X : ℝ) : ℂ) * p0d2_xi X θ m ω

open MeasureTheory ProbabilityTheory in
lemma p0d2_exp_Iic (r : ℝ) (hr : 0 < r) : expMeasure r (Set.Iic 0) = 0 := by
  have := isProbabilityMeasure_expMeasure hr
  have h := cdf_expMeasure_eq hr 0
  rw [cdf_eq_real] at h
  simp only [le_refl, if_true, mul_zero, neg_zero, Real.exp_zero, sub_self] at h
  exact (measureReal_eq_zero_iff).1 h

open MeasureTheory ProbabilityTheory in
lemma p0d2_exp_sq (r : ℝ) (hr : 0 < r) : Integrable (fun x : ℝ => x ^ 2) (expMeasure r) := by
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
lemma p0d2_gap_pos {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (X : CompoundPoissonDemand P) : ∀ᵐ ω ∂P, ∀ n, 0 < X.gap n ω := by
  rw [ae_all_iff]
  intro n
  have h1 : P (X.gap n ⁻¹' Set.Iic 0) = 0 := by
    rw [← Measure.map_apply (X.measurable_gap n) measurableSet_Iic, X.gap_law n]
    exact p0d2_exp_Iic X.lam X.lam_pos
  rw [ae_iff]
  refine measure_mono_null (fun ω hω => ?_) h1
  simp only [Set.mem_setOf_eq, not_lt] at hω
  exact hω

open MeasureTheory ProbabilityTheory InventoryControl in
lemma p0d2_gap_memLp {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (X : CompoundPoissonDemand P) (n : ℕ) : MemLp (X.gap n) 2 P := by
  have h : MemLp (fun x : ℝ => x) 2 (P.map (X.gap n)) := by
    rw [X.gap_law n]
    haveI := isProbabilityMeasure_expMeasure X.lam_pos
    exact (memLp_two_iff_integrable_sq measurable_id.aestronglyMeasurable).2
      (p0d2_exp_sq X.lam X.lam_pos)
  exact (memLp_map_measure_iff measurable_id.aestronglyMeasurable
    (X.measurable_gap n).aemeasurable).1 h

open MeasureTheory ProbabilityTheory InventoryControl in
lemma p0d2_gap_int {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (X : CompoundPoissonDemand P) (n : ℕ) : ∫ ω, X.gap n ω ∂P = p0d2_mu X := by
  unfold p0d2_mu
  rw [← X.gap_law n, integral_map (f := fun x : ℝ => x) (X.measurable_gap n).aemeasurable
    measurable_id.aestronglyMeasurable]

open MeasureTheory ProbabilityTheory InventoryControl in
lemma p0d2_mu_pos {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (X : CompoundPoissonDemand P) : 0 < p0d2_mu X := by
  rw [← p0d2_gap_int X 0]
  have hint : Integrable (X.gap 0) P := (p0d2_gap_memLp X 0).integrable one_le_two
  have hpos : ∀ᵐ ω ∂P, 0 < X.gap 0 ω := (p0d2_gap_pos X).mono fun ω h => h 0
  rw [integral_pos_iff_support_of_nonneg_ae (hpos.mono fun ω h => h.le) hint, pos_iff_ne_zero]
  intro h0
  have h1 := measure_eq_zero_iff_ae_notMem.1 h0
  obtain ⟨ω, h2, h3⟩ := (hpos.and h1).exists
  exact h3 h2.ne'

open MeasureTheory ProbabilityTheory Filter Topology InventoryControl in
lemma p0d2_gap_slln {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (X : CompoundPoissonDemand P) :
    ∀ᵐ ω ∂P, Tendsto (fun n : ℕ => (∑ i ∈ Finset.range n, X.gap i ω) / (n : ℝ)) atTop
      (𝓝 (p0d2_mu X)) := by
  have h := strong_law_ae_real (μ := P) X.gap ((p0d2_gap_memLp X 0).integrable one_le_two)
    (fun i j hij => X.indep_gap.indepFun hij)
    (fun i => ⟨(X.measurable_gap i).aemeasurable, (X.measurable_gap 0).aemeasurable,
      by rw [X.gap_law i, X.gap_law 0]⟩)
  rw [p0d2_gap_int X 0] at h
  exact h

open MeasureTheory ProbabilityTheory InventoryControl in
lemma p0d2_dem_pos {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
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
lemma p0d2_dem_integral {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
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
lemma p0d2_dem_char {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (X : CompoundPoissonDemand P) (θ : ℝ) (m : ℕ) :
    ∫ ω, p0d2_ch θ (X.dem m ω : ℝ) ∂P = p0d2_phi X θ :=
  p0d2_dem_integral X m (fun k => p0d2_ch θ k) (fun k => (p0d2_ch_norm θ k).le)

lemma p0d2_phi_ne_one (size : ℕ → ℝ) (hnn : ∀ k, 0 ≤ size k) (hsum : HasSum size 1)
    (hap : ∀ d : ℕ, 2 ≤ d → ∃ k, 0 < size k ∧ ¬ d ∣ k) (Q r : ℕ) (hr1 : 1 ≤ r) (hrQ : r < Q) :
    ∑' k : ℕ, (size k : ℂ) * p0d2_ch (2 * Real.pi * r / Q) k ≠ 1 := by
  intro h
  have hs : Summable (fun k : ℕ => (size k : ℂ) * p0d2_ch (2 * Real.pi * r / Q) k) := by
    refine Summable.of_norm_bounded hsum.summable fun k => ?_
    rw [norm_mul, p0d2_ch_norm, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (hnn k)]
  have hre : ∑' k : ℕ, size k * Real.cos (2 * Real.pi * r / Q * k) = 1 := by
    have h2 := congrArg Complex.re h
    rw [Complex.re_tsum hs] at h2
    simpa only [Complex.re_ofReal_mul, p0d2_ch, Complex.exp_ofReal_mul_I_re, Complex.one_re]
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
lemma p0d2_indep_prefix {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
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
lemma p0d2_indep_gd {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
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
lemma p0d2_xi_norm {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (X : CompoundPoissonDemand P) (θ : ℝ) (m : ℕ) (ω : Ω) : ‖p0d2_xi X θ m ω‖ = 1 := by
  unfold p0d2_xi; exact p0d2_ch_norm _ _

open MeasureTheory ProbabilityTheory InventoryControl in
lemma p0d2_xi_succ {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (X : CompoundPoissonDemand P) (θ : ℝ) (m : ℕ) (ω : Ω) :
    p0d2_xi X θ (m + 1) ω = p0d2_xi X θ m ω * p0d2_ch θ (X.dem m ω) := by
  unfold p0d2_xi; rw [Finset.sum_range_succ, p0d2_ch_add]

open MeasureTheory ProbabilityTheory InventoryControl in
lemma p0d2_xi_meas {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (X : CompoundPoissonDemand P) (θ : ℝ) (m : ℕ) : Measurable (p0d2_xi X θ m) :=
  (p0d2_ch_meas θ).comp (Finset.measurable_sum _ fun l _ =>
    (measurable_of_countable (Nat.cast : ℕ → ℝ)).comp (X.measurable_dem l))

open MeasureTheory ProbabilityTheory InventoryControl in
lemma p0d2_ch_dem_meas {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (X : CompoundPoissonDemand P) (θ : ℝ) (m : ℕ) :
    Measurable (fun ω => p0d2_ch θ (X.dem m ω : ℝ)) :=
  (p0d2_ch_meas θ).comp ((measurable_of_countable (Nat.cast : ℕ → ℝ)).comp (X.measurable_dem m))

open MeasureTheory ProbabilityTheory InventoryControl in
lemma p0d2_phi_norm {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (X : CompoundPoissonDemand P) (θ : ℝ) : ‖p0d2_phi X θ‖ ≤ 1 := by
  unfold p0d2_phi
  have hn : ∀ k : ℕ, ‖(X.size k : ℂ) * p0d2_ch θ k‖ = X.size k := fun k => by
    rw [norm_mul, p0d2_ch_norm, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (X.size_nonneg k)]
  have hs : Summable (fun k : ℕ => ‖(X.size k : ℂ) * p0d2_ch θ k‖) :=
    X.size_hasSum.summable.congr fun k => (hn k).symm
  refine (norm_tsum_le_tsum_norm hs).trans (le_of_eq ?_)
  rw [tsum_congr hn, X.size_hasSum.tsum_eq]

open MeasureTheory ProbabilityTheory InventoryControl in
lemma p0d2_eta_meas {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (X : CompoundPoissonDemand P) (θ : ℝ) (m : ℕ) : Measurable (p0d2_eta X θ m) :=
  (p0d2_xi_meas X θ m).mul ((p0d2_ch_dem_meas X θ m).sub_const _)

open MeasureTheory ProbabilityTheory InventoryControl in
lemma p0d2_eta_le {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (X : CompoundPoissonDemand P) (θ : ℝ) (m : ℕ) (ω : Ω) : ‖p0d2_eta X θ m ω‖ ≤ 2 := by
  unfold p0d2_eta
  rw [norm_mul, p0d2_xi_norm, one_mul]
  calc ‖p0d2_ch θ (X.dem m ω) - p0d2_phi X θ‖
      ≤ ‖p0d2_ch θ (X.dem m ω)‖ + ‖p0d2_phi X θ‖ := norm_sub_le _ _
    _ ≤ 1 + 1 := by rw [p0d2_ch_norm]; linarith [p0d2_phi_norm X θ]
    _ = 2 := by norm_num

open MeasureTheory ProbabilityTheory InventoryControl in
lemma p0d2_eta_sq {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (X : CompoundPoissonDemand P) (θ : ℝ) (m : ℕ) :
    Integrable (fun ω => ‖p0d2_eta X θ m ω‖ ^ 2) P :=
  Integrable.of_bound ((p0d2_eta_meas X θ m).norm.pow_const 2).aestronglyMeasurable 4
    (Filter.Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      nlinarith [p0d2_eta_le X θ m ω, norm_nonneg (p0d2_eta X θ m ω)])

open MeasureTheory ProbabilityTheory InventoryControl in
lemma p0d2_eta_C {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (X : CompoundPoissonDemand P) (θ : ℝ) (m : ℕ) :
    ∫ ω, ‖p0d2_eta X θ m ω‖ ^ 2 ∂P ≤ 4 := by
  calc ∫ ω, ‖p0d2_eta X θ m ω‖ ^ 2 ∂P ≤ ∫ ω, (4:ℝ) ∂P :=
        integral_mono (p0d2_eta_sq X θ m) (integrable_const _) fun ω => by
          nlinarith [p0d2_eta_le X θ m ω, norm_nonneg (p0d2_eta X θ m ω)]
    _ = 4 := by simp

open MeasureTheory ProbabilityTheory InventoryControl in
lemma p0d2_eta_orth {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (X : CompoundPoissonDemand P) (θ : ℝ) (m m' : ℕ) (hmm : m < m') :
    ∫ ω, p0d2_eta X θ m ω * (starRingEnd ℂ) (p0d2_eta X θ m' ω) ∂P = 0 := by
  let H : (ℕ → ℕ) → ℂ := fun d => p0d2_ch θ (∑ l ∈ Finset.range m, (d l : ℝ))
      * (p0d2_ch θ (d m) - p0d2_phi X θ)
      * (starRingEnd ℂ) (p0d2_ch θ (∑ l ∈ Finset.range m', (d l : ℝ)))
  let G : ℕ → ℂ := fun k => (starRingEnd ℂ) (p0d2_ch θ k - p0d2_phi X θ)
  have hH : ∀ d d' : ℕ → ℕ, (∀ l < m', d l = d' l) → H d = H d' := by
    intro d d' hdd
    have e1 : ∑ l ∈ Finset.range m, (d l : ℝ) = ∑ l ∈ Finset.range m, (d' l : ℝ) :=
      Finset.sum_congr rfl fun l hl => by rw [hdd l ((Finset.mem_range.1 hl).trans hmm)]
    have e2 : ∑ l ∈ Finset.range m', (d l : ℝ) = ∑ l ∈ Finset.range m', (d' l : ℝ) :=
      Finset.sum_congr rfl fun l hl => by rw [hdd l (Finset.mem_range.1 hl)]
    simp only [H, e1, e2, hdd m hmm]
  have hpt : ∀ ω, p0d2_eta X θ m ω * (starRingEnd ℂ) (p0d2_eta X θ m' ω)
      = H (fun l => X.dem l ω) * G (X.dem m' ω) := by
    intro ω
    simp only [p0d2_eta, p0d2_xi, H, G, map_mul]
    ring
  simp_rw [hpt]
  rw [p0d2_indep_prefix X m' H hH G]
  have hint : Integrable (fun ω => p0d2_ch θ (X.dem m' ω : ℝ)) P :=
    Integrable.of_bound (p0d2_ch_dem_meas X θ m').aestronglyMeasurable 1
      (Filter.Eventually.of_forall fun ω => (p0d2_ch_norm _ _).le)
  have hG : ∫ ω, G (X.dem m' ω) ∂P = 0 := by
    simp only [G]
    rw [integral_conj, integral_sub hint (integrable_const _), p0d2_dem_char X θ m', integral_const]
    simp
  rw [hG, mul_zero]

open MeasureTheory ProbabilityTheory InventoryControl in
lemma p0d2_zeta_norm {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (X : CompoundPoissonDemand P) (θ : ℝ) (m : ℕ) (ω : Ω) :
    ‖p0d2_zeta X θ m ω‖ = |X.gap m ω - p0d2_mu X| := by
  unfold p0d2_zeta
  rw [norm_mul, p0d2_xi_norm, mul_one, Complex.norm_real, Real.norm_eq_abs]

open MeasureTheory ProbabilityTheory InventoryControl in
lemma p0d2_zeta_meas {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (X : CompoundPoissonDemand P) (θ : ℝ) (m : ℕ) : Measurable (p0d2_zeta X θ m) :=
  (Complex.measurable_ofReal.comp ((X.measurable_gap m).sub_const _)).mul (p0d2_xi_meas X θ m)

open MeasureTheory ProbabilityTheory InventoryControl in
lemma p0d2_zeta_sq {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (X : CompoundPoissonDemand P) (θ : ℝ) (m : ℕ) :
    Integrable (fun ω => ‖p0d2_zeta X θ m ω‖ ^ 2) P := by
  have h := (memLp_two_iff_integrable_sq
    (((X.measurable_gap m).sub_const (p0d2_mu X)).aestronglyMeasurable)).1
    ((p0d2_gap_memLp X m).sub (memLp_const (p0d2_mu X)))
  refine h.congr (Filter.Eventually.of_forall fun ω => ?_)
  simp only [p0d2_zeta_norm, sq_abs]

open MeasureTheory ProbabilityTheory InventoryControl in
lemma p0d2_zeta_C {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (X : CompoundPoissonDemand P) (θ : ℝ) (m : ℕ) :
    ∫ ω, ‖p0d2_zeta X θ m ω‖ ^ 2 ∂P = ∫ x, (x - p0d2_mu X) ^ 2 ∂(expMeasure X.lam) := by
  simp only [p0d2_zeta_norm, sq_abs]
  rw [← X.gap_law m, integral_map (f := fun x : ℝ => (x - p0d2_mu X) ^ 2)
    (X.measurable_gap m).aemeasurable ((measurable_id.sub_const _).pow_const 2).aestronglyMeasurable]

open MeasureTheory ProbabilityTheory InventoryControl in
lemma p0d2_zeta_orth {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (X : CompoundPoissonDemand P) (θ : ℝ) (m m' : ℕ) (hmm : m < m') :
    ∫ ω, p0d2_zeta X θ m ω * (starRingEnd ℂ) (p0d2_zeta X θ m' ω) ∂P = 0 := by
  let A : (ℕ → ℝ) → ℂ := fun g => (((g m - p0d2_mu X) * (g m' - p0d2_mu X) : ℝ) : ℂ)
  let B : (ℕ → ℕ) → ℂ := fun d => p0d2_ch θ (∑ l ∈ Finset.range m, (d l : ℝ))
      * (starRingEnd ℂ) (p0d2_ch θ (∑ l ∈ Finset.range m', (d l : ℝ)))
  have hA : Measurable A := Complex.measurable_ofReal.comp
    (((measurable_pi_apply m).sub_const _).mul ((measurable_pi_apply m').sub_const _))
  have hB : Measurable B := by
    have h1 : ∀ n, Measurable (fun d : ℕ → ℕ => ∑ l ∈ Finset.range n, (d l : ℝ)) := fun n =>
      Finset.measurable_sum _ fun l _ =>
        (measurable_of_countable (Nat.cast : ℕ → ℝ)).comp (measurable_pi_apply l)
    exact ((p0d2_ch_meas θ).comp (h1 m)).mul
      (Complex.continuous_conj.measurable.comp ((p0d2_ch_meas θ).comp (h1 m')))
  have hpt : ∀ ω, p0d2_zeta X θ m ω * (starRingEnd ℂ) (p0d2_zeta X θ m' ω)
      = A (fun l => X.gap l ω) * B (fun l => X.dem l ω) := by
    intro ω
    simp only [p0d2_zeta, p0d2_xi, A, B, map_mul, Complex.conj_ofReal]
    push_cast; ring
  simp_rw [hpt]
  rw [p0d2_indep_gd X A hA B hB]
  have hA0 : ∫ ω, A (fun l => X.gap l ω) ∂P = 0 := by
    simp only [A]
    rw [integral_complex_ofReal]
    have hind := (X.indep_gap.indepFun hmm.ne).integral_fun_comp_mul_comp
      (f := fun x : ℝ => x - p0d2_mu X) (g := fun x : ℝ => x - p0d2_mu X)
      (X.measurable_gap m).aemeasurable (X.measurable_gap m').aemeasurable
      (measurable_id.sub_const _).aestronglyMeasurable (measurable_id.sub_const _).aestronglyMeasurable
    rw [hind, integral_sub ((p0d2_gap_memLp X m).integrable one_le_two) (integrable_const _),
      p0d2_gap_int, integral_const]
    simp
  rw [hA0, zero_mul]

open MeasureTheory ProbabilityTheory Filter Topology InventoryControl in
lemma p0d2_zeta_b {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (X : CompoundPoissonDemand P) (θ : ℝ) :
    ∀ᵐ ω ∂P, (∀ m, ‖p0d2_zeta X θ m ω‖ ≤ |X.gap m ω| + p0d2_mu X) ∧
      Tendsto (fun n : ℕ => (∑ m ∈ Finset.range n, (|X.gap m ω| + p0d2_mu X)) / (n : ℝ)) atTop
        (𝓝 (p0d2_mu X + p0d2_mu X)) := by
  filter_upwards [p0d2_gap_slln X, p0d2_gap_pos X] with ω h1 h2
  refine ⟨fun m => ?_, ?_⟩
  · rw [p0d2_zeta_norm]
    exact abs_le.2 ⟨by linarith [neg_abs_le (X.gap m ω), p0d2_mu_pos X],
      by linarith [le_abs_self (X.gap m ω), p0d2_mu_pos X]⟩
  · have h3 := h1.add_const (p0d2_mu X)
    refine h3.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
    have h2' : ∀ m, |X.gap m ω| = X.gap m ω := fun m => abs_of_pos (h2 m)
    simp only [h2', Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    rw [add_div, mul_div_cancel_left₀ _ hn']

open MeasureTheory ProbabilityTheory Filter Topology InventoryControl in
lemma p0d2_char_avg {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (X : CompoundPoissonDemand P) (θ : ℝ) (hφ : p0d2_phi X θ ≠ 1) :
    ∀ᵐ ω ∂P, Tendsto (fun n : ℕ => (∑ m ∈ Finset.range n, (X.gap m ω : ℂ) * p0d2_xi X θ m ω)
      / (n : ℂ)) atTop (𝓝 0) := by
  have hη := p0d2_slln_orth (p0d2_eta X θ) 4 (p0d2_eta_meas X θ) (p0d2_eta_sq X θ)
    (p0d2_eta_C X θ) (p0d2_eta_orth X θ) (fun _ _ => (2:ℝ)) (fun _ => (2:ℝ))
    (Filter.Eventually.of_forall fun ω => ⟨fun m => p0d2_eta_le X θ m ω, p0d2_const_avg 2⟩)
  have hζ := p0d2_slln_orth (p0d2_zeta X θ) (∫ x, (x - p0d2_mu X) ^ 2 ∂(expMeasure X.lam))
    (p0d2_zeta_meas X θ) (p0d2_zeta_sq X θ) (fun m => (p0d2_zeta_C X θ m).le)
    (p0d2_zeta_orth X θ) (fun m ω => |X.gap m ω| + p0d2_mu X) (fun _ => p0d2_mu X + p0d2_mu X)
    (p0d2_zeta_b X θ)
  filter_upwards [hη, hζ] with ω h1 h2
  have h1φ : (1 - p0d2_phi X θ) ≠ 0 := sub_ne_zero.2 (Ne.symm hφ)
  have hid : ∀ n : ℕ, ∑ m ∈ Finset.range n, (X.gap m ω : ℂ) * p0d2_xi X θ m ω
      = (p0d2_mu X : ℂ) / (1 - p0d2_phi X θ) * ((∑ m ∈ Finset.range n, p0d2_eta X θ m ω)
          - p0d2_xi X θ n ω + p0d2_xi X θ 0 ω)
        + ∑ m ∈ Finset.range n, p0d2_zeta X θ m ω := by
    intro n
    have hη' : ∑ m ∈ Finset.range n, p0d2_eta X θ m ω
        = (p0d2_xi X θ n ω - p0d2_xi X θ 0 ω)
          + (1 - p0d2_phi X θ) * ∑ m ∈ Finset.range n, p0d2_xi X θ m ω := by
      rw [← Finset.sum_range_sub (fun m => p0d2_xi X θ m ω), Finset.mul_sum,
        ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun m _ => ?_
      simp only [p0d2_eta, p0d2_xi_succ]
      ring
    have hζ' : ∑ m ∈ Finset.range n, p0d2_zeta X θ m ω
        = ∑ m ∈ Finset.range n, (X.gap m ω : ℂ) * p0d2_xi X θ m ω
          - (p0d2_mu X : ℂ) * ∑ m ∈ Finset.range n, p0d2_xi X θ m ω := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun m _ => ?_
      simp only [p0d2_zeta]; push_cast; ring
    rw [hζ', hη']
    have e : p0d2_xi X θ n ω - p0d2_xi X θ 0 ω
        + (1 - p0d2_phi X θ) * ∑ m ∈ Finset.range n, p0d2_xi X θ m ω
        - p0d2_xi X θ n ω + p0d2_xi X θ 0 ω
        = (1 - p0d2_phi X θ) * ∑ m ∈ Finset.range n, p0d2_xi X θ m ω := by ring
    rw [e, ← mul_assoc, div_mul_cancel₀ _ h1φ]
    ring
  have hxn : Tendsto (fun n : ℕ => p0d2_xi X θ n ω / (n : ℂ)) atTop (𝓝 0) := by
    refine squeeze_zero_norm (fun n => ?_) (tendsto_const_div_atTop_nhds_zero_nat (1:ℝ))
    rw [norm_div, p0d2_xi_norm, Complex.norm_natCast]
  have hx0 : Tendsto (fun n : ℕ => p0d2_xi X θ 0 ω / (n : ℂ)) atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat _
  have hlim := (((h1.sub hxn).add hx0).const_mul ((p0d2_mu X : ℂ) / (1 - p0d2_phi X θ))).add h2
  simp only [sub_zero, add_zero, mul_zero] at hlim
  refine hlim.congr fun n => ?_
  rw [hid n]; ring

lemma p0d2_fourier (Q : ℕ) (hQ : 0 < Q) (y : ℤ) :
    ∑ r ∈ Finset.range Q, p0d2_ch (2 * Real.pi * r / Q) (y : ℝ)
      = if (Q : ℤ) ∣ y then (Q : ℂ) else 0 := by
  have hprim := Complex.isPrimitiveRoot_exp Q hQ.ne'
  set ζ := Complex.exp (2 * ↑Real.pi * Complex.I / ↑Q) with hζ
  have hw : ∀ r : ℕ, p0d2_ch (2 * Real.pi * r / Q) (y : ℝ) = (ζ ^ y) ^ r := by
    intro r
    rw [hζ, ← Complex.exp_int_mul, ← Complex.exp_nat_mul, p0d2_ch]
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
lemma p0d2_band_iff (R : ℤ) (Q : ℕ) (hQ : 0 < Q) (j : ℤ) (hj1 : R + 1 ≤ j) (hj2 : j ≤ R + Q)
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
lemma p0d2_ctime (g f : ℕ → ℝ) (μ L : ℝ) (hμ : 0 < μ)
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
lemma p0d2_arr_mono {Ω : Type*} [MeasurableSpace Ω] {P : MeasureTheory.Measure Ω}
    (X : CompoundPoissonDemand P) (ω : Ω) (hg : ∀ n, 0 < X.gap n ω) (a b : ℕ) (hab : a ≤ b) :
    X.arrival a ω ≤ X.arrival b ω := by
  unfold CompoundPoissonDemand.arrival
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hab) (fun i _ _ => (hg i).le)

open Filter Topology InventoryControl in
lemma p0d2_arr_tendsto {Ω : Type*} [MeasurableSpace Ω] {P : MeasureTheory.Measure Ω}
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
lemma p0d2_count_eq {Ω : Type*} [MeasurableSpace Ω] {P : MeasureTheory.Measure Ω}
    (X : CompoundPoissonDemand P) (ω : Ω) (hg : ∀ n, 0 < X.gap n ω) (m : ℕ) (t : ℝ)
    (h1 : X.arrival m ω ≤ t) (h2 : t < X.arrival (m + 1) ω) : X.count t ω = m := by
  unfold CompoundPoissonDemand.count
  refine IsGreatest.csSup_eq ⟨h1, fun n hn => ?_⟩
  by_contra hlt
  push_neg at hlt
  have := p0d2_arr_mono X ω hg (m + 1) n hlt
  simp only [Set.mem_setOf_eq] at hn
  linarith

open Filter Topology InventoryControl in
lemma p0d2_count_bracket {Ω : Type*} [MeasurableSpace Ω] {P : MeasureTheory.Measure Ω}
    (X : CompoundPoissonDemand P) (ω : Ω) (hg : ∀ n, 0 < X.gap n ω)
    (hinf : Tendsto (fun n => X.arrival n ω) atTop atTop) (T : ℝ) (hT : 0 ≤ T) :
    X.arrival (X.count T ω) ω ≤ T ∧ T < X.arrival (X.count T ω + 1) ω := by
  have hex : ∃ k, T < X.arrival (k + 1) ω := by
    obtain ⟨k, hk⟩ := (hinf.eventually_gt_atTop T).exists
    exact ⟨k, lt_of_lt_of_le hk (p0d2_arr_mono X ω hg k (k + 1) (Nat.le_succ k))⟩
  classical
  have hk1 : T < X.arrival (Nat.find hex + 1) ω := Nat.find_spec hex
  have hk2 : X.arrival (Nat.find hex) ω ≤ T := by
    rcases Nat.eq_zero_or_pos (Nat.find hex) with h0 | hpos
    · rw [h0]; simp [CompoundPoissonDemand.arrival, hT]
    · obtain ⟨j, hj⟩ : ∃ j, Nat.find hex = j + 1 := ⟨Nat.find hex - 1, by omega⟩
      have := Nat.find_min hex (show j < Nat.find hex by omega)
      push_neg at this
      rw [hj]; exact this
  rw [p0d2_count_eq X ω hg (Nat.find hex) T hk2 hk1]
  exact ⟨hk2, hk1⟩

open Filter Topology InventoryControl in
lemma p0d2_count_mono {Ω : Type*} [MeasurableSpace Ω] {P : MeasureTheory.Measure Ω}
    (X : CompoundPoissonDemand P) (ω : Ω) (hg : ∀ n, 0 < X.gap n ω)
    (hinf : Tendsto (fun n => X.arrival n ω) atTop atTop) : Monotone (fun t => X.count t ω) := by
  intro s t hst
  unfold CompoundPoissonDemand.count
  apply csSup_le_csSup'
  · obtain ⟨K, hK⟩ := (hinf.eventually_gt_atTop t).exists
    refine ⟨K, fun n hn => ?_⟩
    by_contra hlt
    push_neg at hlt
    have := p0d2_arr_mono X ω hg K n hlt.le
    simp only [Set.mem_setOf_eq] at hn
    linarith
  · intro n hn
    simp only [Set.mem_setOf_eq] at hn ⊢
    linarith

open MeasureTheory Filter Topology InventoryControl in
lemma p0d2_integral_decomp {Ω : Type*} [MeasurableSpace Ω] {P : MeasureTheory.Measure Ω}
    (X : CompoundPoissonDemand P) (ω : Ω) (hg : ∀ n, 0 < X.gap n ω)
    (hinf : Tendsto (fun n => X.arrival n ω) atTop atTop) (f : ℕ → ℝ) (hf : ∀ n, |f n| ≤ 1)
    (T : ℝ) (hT : 0 ≤ T) :
    ∫ t in (0:ℝ)..T, f (X.count t ω) = ∑ m ∈ Finset.range (X.count T ω), X.gap m ω * f m
      + (T - X.arrival (X.count T ω) ω) * f (X.count T ω) := by
  have hmeas : Measurable (fun t => f (X.count t ω)) :=
    (measurable_of_countable f).comp (p0d2_count_mono X ω hg hinf).measurable
  have hII : ∀ a b : ℝ, IntervalIntegrable (fun t => f (X.count t ω)) volume a b := by
    intro a b
    refine (intervalIntegrable_const (c := (1:ℝ))).mono_fun hmeas.aestronglyMeasurable ?_
    exact Filter.Eventually.of_forall fun t => by simpa [Real.norm_eq_abs] using hf (X.count t ω)
  have harr0 : X.arrival 0 ω = 0 := by simp [CompoundPoissonDemand.arrival]
  have hpiece : ∀ k, ∫ t in (X.arrival k ω)..(X.arrival (k + 1) ω), f (X.count t ω)
      = X.gap k ω * f k := by
    intro k
    have hle : X.arrival k ω ≤ X.arrival (k + 1) ω := p0d2_arr_mono X ω hg k (k + 1) (Nat.le_succ k)
    rw [intervalIntegral.integral_congr_ae (g := fun _ => f k) ?_, intervalIntegral.integral_const,
      smul_eq_mul]
    · congr 1
      simp [CompoundPoissonDemand.arrival, Finset.sum_range_succ]
    · filter_upwards [Measure.ae_ne volume (X.arrival (k + 1) ω)] with t ht htI
      rw [Set.uIoc_of_le hle] at htI
      exact congrArg f (p0d2_count_eq X ω hg k t htI.1.le (lt_of_le_of_ne htI.2 ht))
  obtain ⟨h1, h2⟩ := p0d2_count_bracket X ω hg hinf T hT
  have hlast : ∫ t in (X.arrival (X.count T ω) ω)..T, f (X.count t ω)
      = (T - X.arrival (X.count T ω) ω) * f (X.count T ω) := by
    rw [intervalIntegral.integral_congr (g := fun _ => f (X.count T ω)) ?_,
      intervalIntegral.integral_const, smul_eq_mul]
    intro t ht
    rw [Set.uIcc_of_le h1] at ht
    exact congrArg f (p0d2_count_eq X ω hg (X.count T ω) t ht.1 (lt_of_le_of_lt ht.2 h2))
  have hsum := intervalIntegral.sum_integral_adjacent_intervals (a := fun k => X.arrival k ω)
    (n := X.count T ω) (μ := volume) (fun k _ => hII _ _)
  simp only [harr0] at hsum
  rw [← intervalIntegral.integral_add_adjacent_intervals (hII 0 (X.arrival (X.count T ω) ω))
    (hII _ T), hlast, ← hsum]
  simp only [hpiece]

lemma p0d2_ite01 (c : Prop) [Decidable c] :
    0 ≤ (if c then (1:ℝ) else 0) ∧ (if c then (1:ℝ) else 0) ≤ 1 ∧ |if c then (1:ℝ) else 0| ≤ 1 := by
  split_ifs <;> norm_num

open MeasureTheory ProbabilityTheory Filter Topology InventoryControl in
lemma p0d2_discrete {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (X : CompoundPoissonDemand P) (R : ℤ) (Q : ℕ) (hQ : 0 < Q) (y0 j : ℤ)
    (hj1 : R + 1 ≤ j) (hj2 : j ≤ R + Q) :
    ∀ᵐ ω ∂P, Tendsto (fun n : ℕ => (∑ m ∈ Finset.range n,
        X.gap m ω * (if reduceToBand R Q (y0 - (X.cumDemand m ω : ℤ)) = j then (1:ℝ) else 0))
          / (n : ℝ)) atTop
      (𝓝 (p0d2_mu X * (1 / (Q : ℝ)))) := by
  have hchar : ∀ᵐ ω ∂P, ∀ r : ℕ, r < Q → Tendsto (fun n : ℕ => (∑ m ∈ Finset.range n,
      (X.gap m ω : ℂ) * p0d2_xi X (2 * Real.pi * r / Q) m ω) / (n : ℂ)) atTop
      (𝓝 (if r = 0 then (p0d2_mu X : ℂ) else 0)) := by
    rw [ae_all_iff]
    intro r
    by_cases hr : r < Q
    · rcases Nat.eq_zero_or_pos r with h0 | hpos
      · subst h0
        filter_upwards [p0d2_gap_slln X] with ω hω _
        rw [if_pos rfl]
        have := (Complex.continuous_ofReal.tendsto _).comp hω
        refine this.congr fun n => ?_
        simp [p0d2_xi, p0d2_ch]
      · filter_upwards [p0d2_char_avg X _ (p0d2_phi_ne_one X.size X.size_nonneg X.size_hasSum
          X.size_aperiodic Q r hpos hr)] with ω hω _
        rw [if_neg hpos.ne']
        exact hω
    · exact Filter.Eventually.of_forall fun ω h => absurd h hr
  filter_upwards [hchar] with ω hω
  set κ : ℕ → ℂ := fun r => p0d2_ch (2 * Real.pi * r / Q) ((j - y0 : ℤ) : ℝ) with hκ
  have hQne : (Q : ℂ) ≠ 0 := by exact_mod_cast hQ.ne'
  have hind : ∀ m, 0 ≤ m →
      ((X.gap m ω * (if reduceToBand R Q (y0 - (X.cumDemand m ω : ℤ)) = j then (1:ℝ) else 0)
          : ℝ) : ℂ)
        = (1 / (Q : ℂ)) * ∑ r ∈ Finset.range Q,
            κ r * ((X.gap m ω : ℂ) * p0d2_xi X (2 * Real.pi * r / Q) m ω) := by
    intro m _
    have hiff := p0d2_band_iff R Q hQ j hj1 hj2 y0 (X.cumDemand m ω : ℤ)
    have hF := p0d2_fourier Q hQ ((X.cumDemand m ω : ℤ) + (j - y0))
    have hsplit : ∀ r : ℕ, p0d2_ch (2 * Real.pi * r / Q)
        ((((X.cumDemand m ω : ℤ) + (j - y0) : ℤ)) : ℝ)
        = κ r * p0d2_xi X (2 * Real.pi * r / Q) m ω := by
      intro r
      simp only [hκ, p0d2_xi]
      rw [mul_comm, ← p0d2_ch_add]
      congr 1
      unfold CompoundPoissonDemand.cumDemand
      push_cast
      ring
    have hsum : ∑ r ∈ Finset.range Q,
        κ r * ((X.gap m ω : ℂ) * p0d2_xi X (2 * Real.pi * r / Q) m ω)
        = (X.gap m ω : ℂ) * ∑ r ∈ Finset.range Q, p0d2_ch (2 * Real.pi * r / Q)
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
      κ r * ((X.gap m ω : ℂ) * p0d2_xi X (2 * Real.pi * r / Q) m ω)) / (n : ℂ)) atTop
      (𝓝 ((p0d2_mu X : ℂ) * (1 / (Q : ℂ)))) := by
    have h1 : Tendsto (fun n : ℕ => (1 / (Q : ℂ)) * ∑ r ∈ Finset.range Q, κ r *
        ((∑ m ∈ Finset.range n, (X.gap m ω : ℂ) * p0d2_xi X (2 * Real.pi * r / Q) m ω)
          / (n : ℂ))) atTop
        (𝓝 ((1 / (Q : ℂ)) * ∑ r ∈ Finset.range Q, κ r * (if r = 0 then (p0d2_mu X : ℂ) else 0))) :=
      tendsto_const_nhds.mul (tendsto_finset_sum _ fun r hr =>
        tendsto_const_nhds.mul (hω r (Finset.mem_range.1 hr)))
    have hκ0 : κ 0 = 1 := by simp [hκ, p0d2_ch]
    have hval : (1 / (Q : ℂ)) * ∑ r ∈ Finset.range Q, κ r * (if r = 0 then (p0d2_mu X : ℂ) else 0)
        = (p0d2_mu X : ℂ) * (1 / (Q : ℂ)) := by
      rw [Finset.sum_eq_single 0 (fun b _ hb => by rw [if_neg hb, mul_zero])
        (fun h => absurd (Finset.mem_range.2 hQ) h), if_pos rfl, hκ0, one_mul, mul_comm]
    rw [hval] at h1
    refine h1.congr fun n => ?_
    simp only [Finset.mul_sum, Finset.sum_div]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun r _ => ?_
    ring
  have hC := p0d2_event_avg
    (fun m => ((X.gap m ω * (if reduceToBand R Q (y0 - (X.cumDemand m ω : ℤ)) = j
      then (1:ℝ) else 0) : ℝ) : ℂ)) _ 0 hind _ hlimC
  have hR := (Complex.continuous_re.tendsto _).comp hC
  have hval : ((p0d2_mu X : ℂ) * (1 / (Q : ℂ))).re = p0d2_mu X * (1 / (Q : ℝ)) := by
    rw [show (p0d2_mu X : ℂ) * (1 / (Q : ℂ)) = ((p0d2_mu X * (1 / (Q : ℝ)) : ℝ) : ℂ) by
      push_cast; ring, Complex.ofReal_re]
  rw [hval] at hR
  refine hR.congr fun n => ?_
  simp only [Function.comp]
  rw [← Complex.ofReal_natCast, ← Complex.ofReal_sum, ← Complex.ofReal_div, Complex.ofReal_re]

open MeasureTheory ProbabilityTheory Filter Topology InventoryControl in
lemma p0d2_uniform {Ω : Type*} [MeasurableSpace Ω] {P : MeasureTheory.Measure Ω}
    [MeasureTheory.IsProbabilityMeasure P] (X : CompoundPoissonDemand P) (R : ℤ) (Q : ℕ)
    (hQ : 0 < Q) (y0 : ℤ) (j : ℤ) (hj1 : R + 1 ≤ j) (hj2 : j ≤ R + Q) :
    ∀ᵐ ω ∂P, Filter.Tendsto
      (fun T : ℝ => (1 / T) * ∫ t in (0 : ℝ)..T,
          (if reduceToBand R Q (y0 - (X.cumDemand (X.count t ω) ω : ℤ)) = j then (1 : ℝ) else 0))
      Filter.atTop (nhds (1 / (Q : ℝ))) := by
  filter_upwards [p0d2_gap_pos X, p0d2_gap_slln X, p0d2_discrete X R Q hQ y0 j hj1 hj2]
    with ω hg hG hF
  have hμ := p0d2_mu_pos X
  have hinf := p0d2_arr_tendsto X ω (p0d2_mu X) hμ hG
  exact p0d2_ctime (fun n => X.gap n ω)
    (fun n => if reduceToBand R Q (y0 - (X.cumDemand n ω : ℤ)) = j then (1 : ℝ) else 0)
    (p0d2_mu X) (1 / (Q : ℝ)) hμ hg (fun n => (p0d2_ite01 _).1) (fun n => (p0d2_ite01 _).2.1)
    hG hF (fun T => X.count T ω) (fun T hT => p0d2_count_bracket X ω hg hinf T hT)
    (fun T => ∫ t in (0 : ℝ)..T,
      (if reduceToBand R Q (y0 - (X.cumDemand (X.count t ω) ω : ℤ)) = j then (1 : ℝ) else 0))
    (fun T hT => p0d2_integral_decomp X ω hg hinf
      (fun n => if reduceToBand R Q (y0 - (X.cumDemand n ω : ℤ)) = j then (1 : ℝ) else 0)
      (fun n => (p0d2_ite01 _).2.2) T hT)

-- ============ Part E: from indicators to the cost average (0d26653f) ============

open InventoryControl in
lemma p0d2_rep (g : ℤ → ℝ) (R : ℤ) (Q : ℕ) (hQ : 0 < Q) (z : ℤ) :
    g (reduceToBand R Q z) = ∑ k ∈ Finset.range Q,
      g (R + 1 + (k : ℤ)) * (if reduceToBand R Q z = R + 1 + (k : ℤ) then (1 : ℝ) else 0) := by
  have hQ' : (0 : ℤ) < Q := by exact_mod_cast hQ
  set w : ℤ := (z - (R + 1)) % (Q : ℤ) with hw
  have hw0 : 0 ≤ w := Int.emod_nonneg _ hQ'.ne'
  have hw1 : w < Q := Int.emod_lt_of_pos _ hQ'
  have hrtb : reduceToBand R Q z = R + 1 + w := rfl
  have hmem : w.toNat ∈ Finset.range Q := Finset.mem_range.2 (by omega)
  rw [Finset.sum_eq_single_of_mem w.toNat hmem]
  · rw [hrtb, Int.toNat_of_nonneg hw0, if_pos rfl, mul_one]
  · intro k _ hk
    rw [hrtb, if_neg, mul_zero]
    intro hc
    apply hk
    omega

open InventoryControl in
lemma p0d2_bound (g : ℤ → ℝ) (R : ℤ) (Q : ℕ) (hQ : 0 < Q) (z : ℤ) :
    |g (reduceToBand R Q z)| ≤ ∑ k ∈ Finset.range Q, |g (R + 1 + (k : ℤ))| := by
  rw [p0d2_rep g R Q hQ z]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum fun k _ => ?_)
  rw [abs_mul]
  refine mul_le_of_le_one_right (abs_nonneg _) ?_
  split_ifs <;> norm_num

open MeasureTheory in
lemma p0d2_ii (f : ℝ → ℝ) (hf : Measurable f) (K : ℝ) (hK : ∀ t, |f t| ≤ K) (a b : ℝ) :
    IntervalIntegrable f volume a b := by
  refine (intervalIntegrable_const (c := K)).mono_fun hf.aestronglyMeasurable ?_
  exact Filter.Eventually.of_forall fun t => by
    simp only [Real.norm_eq_abs]
    exact le_trans (hK t) (le_abs_self K)

open MeasureTheory Filter Topology InventoryControl in
lemma p0d2_avg (g : ℤ → ℝ) (W : ℝ → ℤ) (hW : Measurable W) (R : ℤ) (Q : ℕ) (hQ : 0 < Q)
    (hU : ∀ k : ℕ, k < Q → Tendsto (fun T : ℝ => (1 / T) * ∫ t in (0:ℝ)..T,
      (if reduceToBand R Q (W t) = R + 1 + (k : ℤ) then (1 : ℝ) else 0)) atTop (𝓝 (1 / (Q : ℝ)))) :
    Tendsto (fun T : ℝ => (1 / T) * ∫ t in (0:ℝ)..T, g (reduceToBand R Q (W t))) atTop
      (𝓝 ((∑ k ∈ Finset.range Q, g (R + 1 + (k : ℤ))) / (Q : ℝ))) := by
  have hII : ∀ (k : ℕ) (a b : ℝ), IntervalIntegrable
      (fun t => if reduceToBand R Q (W t) = R + 1 + (k : ℤ) then (1 : ℝ) else 0) volume a b := by
    intro k a b
    refine p0d2_ii _ ((measurable_of_countable
      (fun z : ℤ => if reduceToBand R Q z = R + 1 + (k : ℤ) then (1 : ℝ) else 0)).comp hW) 1
      (fun t => ?_) a b
    simp only [Function.comp]
    split_ifs <;> norm_num
  have hint : ∀ T : ℝ, ∫ t in (0:ℝ)..T, g (reduceToBand R Q (W t))
      = ∑ k ∈ Finset.range Q, g (R + 1 + (k : ℤ)) * ∫ t in (0:ℝ)..T,
          (if reduceToBand R Q (W t) = R + 1 + (k : ℤ) then (1 : ℝ) else 0) := by
    intro T
    rw [intervalIntegral.integral_congr (fun t _ => p0d2_rep g R Q hQ (W t)),
      intervalIntegral.integral_finset_sum (fun k _ => (hII k 0 T).const_mul _)]
    refine Finset.sum_congr rfl fun k _ => ?_
    exact intervalIntegral.integral_const_mul _ _
  have hsum := tendsto_finset_sum (Finset.range Q)
    (fun k hk => (hU k (Finset.mem_range.1 hk)).const_mul (g (R + 1 + (k : ℤ))))
  have hval : ∑ k ∈ Finset.range Q, g (R + 1 + (k : ℤ)) * (1 / (Q : ℝ))
      = (∑ k ∈ Finset.range Q, g (R + 1 + (k : ℤ))) / (Q : ℝ) := by
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  rw [hval] at hsum
  refine hsum.congr fun T => ?_
  rw [hint T, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

open MeasureTheory Filter Topology in
lemma p0d2_shift (g : ℤ → ℝ) (Z : ℝ → ℤ) (hZ : Measurable Z) (M : ℝ) (hM : ∀ s, |g (Z s)| ≤ M)
    (y0 : ℤ) (L : ℝ) (hL : 0 ≤ L) (ℓ : ℝ)
    (hlim : Tendsto (fun T : ℝ => (1 / T) * ∫ t in (0:ℝ)..T, g (Z t)) atTop (𝓝 ℓ)) :
    Tendsto (fun T : ℝ => (1 / T) * ∫ t in (0:ℝ)..T, g (if t < L then y0 else Z (t - L)))
      atTop (𝓝 ℓ) := by
  have hM0 : 0 ≤ M := le_trans (abs_nonneg _) (hM 0)
  have hFm : Measurable (fun t : ℝ => g (if t < L then y0 else Z (t - L))) :=
    (measurable_of_countable g).comp
      (Measurable.ite measurableSet_Iio measurable_const (hZ.comp (measurable_id.sub_const L)))
  have hFb : ∀ t : ℝ, |g (if t < L then y0 else Z (t - L))| ≤ |g y0| + M := by
    intro t
    split_ifs
    · linarith
    · linarith [hM (t - L), abs_nonneg (g y0)]
  have hGm : Measurable (fun t : ℝ => g (Z t)) := (measurable_of_countable g).comp hZ
  have heq : ∀ T : ℝ, L ≤ T → ∫ t in (0:ℝ)..T, g (if t < L then y0 else Z (t - L))
      = L * g y0 + ∫ t in (0:ℝ)..(T - L), g (Z t) := by
    intro T hLT
    rw [← intervalIntegral.integral_add_adjacent_intervals (p0d2_ii _ hFm _ hFb 0 L)
      (p0d2_ii _ hFm _ hFb L T)]
    have e1 : ∫ t in (0:ℝ)..L, g (if t < L then y0 else Z (t - L)) = L * g y0 := by
      rw [intervalIntegral.integral_congr_ae (g := fun _ => g y0) ?_,
        intervalIntegral.integral_const, smul_eq_mul, sub_zero]
      filter_upwards [Measure.ae_ne volume L] with t ht htI
      rw [Set.uIoc_of_le hL] at htI
      rw [if_pos (lt_of_le_of_ne htI.2 ht)]
    have e2 : ∫ t in L..T, g (if t < L then y0 else Z (t - L))
        = ∫ t in (0:ℝ)..(T - L), g (Z t) := by
      rw [intervalIntegral.integral_congr (g := fun t => g (Z (t - L))) ?_,
        intervalIntegral.integral_comp_sub_right (fun t => g (Z t)) L, sub_self]
      intro t ht
      rw [Set.uIcc_of_le hLT] at ht
      simp only [if_neg (not_lt.2 ht.1)]
    rw [e1, e2]
  have h1 : Tendsto (fun T : ℝ => 1 - L * T⁻¹) atTop (𝓝 (1 - L * 0)) :=
    tendsto_const_nhds.sub (tendsto_const_nhds.mul tendsto_inv_atTop_zero)
  have h2 : Tendsto (fun T : ℝ => (1 / (T + -L)) * ∫ t in (0:ℝ)..(T + -L), g (Z t)) atTop (𝓝 ℓ) :=
    hlim.comp (tendsto_atTop_add_const_right atTop (-L) tendsto_id)
  have h3 : Tendsto (fun T : ℝ => L * g y0 * T⁻¹) atTop (𝓝 (L * g y0 * 0)) :=
    tendsto_const_nhds.mul tendsto_inv_atTop_zero
  have hc := h3.add (h1.mul h2)
  have hlv : L * g y0 * 0 + (1 - L * 0) * ℓ = ℓ := by ring
  rw [hlv] at hc
  refine hc.congr' ?_
  filter_upwards [eventually_gt_atTop L] with T hT
  have hT0 : T ≠ 0 := by intro h0; rw [h0] at hT; linarith
  have hTL : T + -L ≠ 0 := by intro h0; linarith
  rw [heq T hT.le, ← sub_eq_add_neg]
  have hTL' : T - L ≠ 0 := by rwa [sub_eq_add_neg]
  field_simp

open MeasureTheory ProbabilityTheory Filter Topology InventoryControl in
lemma p097_reduced {Ω : Type*} [MeasurableSpace Ω] {P : MeasureTheory.Measure Ω}
    [MeasureTheory.IsProbabilityMeasure P] (X : CompoundPoissonDemand P) (D : DiscreteDemand)
    (h b1 L : ℝ) (hL : 0 ≤ L) (R : ℤ) (Q : ℕ) (hQ : 0 < Q) (y0 : ℤ) :
    ∀ᵐ ω ∂P, Filter.Tendsto
      (fun T : ℝ => (1 / T) * ∫ t in (0 : ℝ)..T,
          sPolicyCost D h b1 (if t < L then y0
            else reduceToBand R Q (y0 - (X.cumDemand (X.count (t - L) ω) ω : ℤ))))
      Filter.atTop (nhds (windowCost D h b1 Q R / Q)) := by
  have hU : ∀ᵐ ω ∂P, ∀ k : ℕ, k < Q → Tendsto (fun T : ℝ => (1 / T) * ∫ t in (0 : ℝ)..T,
      (if reduceToBand R Q (y0 - (X.cumDemand (X.count t ω) ω : ℤ)) = R + 1 + (k : ℤ)
        then (1 : ℝ) else 0)) atTop (𝓝 (1 / (Q : ℝ))) := by
    rw [ae_all_iff]
    intro k
    by_cases hk : k < Q
    · filter_upwards [p0d2_uniform X R Q hQ y0 (R + 1 + (k : ℤ)) (by omega) (by omega)]
        with ω hω _
      exact hω
    · exact Filter.Eventually.of_forall fun ω hk' => absurd hk' hk
  filter_upwards [p0d2_gap_pos X, p0d2_gap_slln X, hU] with ω hg hG hUω
  have hinf := p0d2_arr_tendsto X ω (p0d2_mu X) (p0d2_mu_pos X) hG
  have hN : Measurable (fun t => X.count t ω) := (p0d2_count_mono X ω hg hinf).measurable
  have hW : Measurable (fun t : ℝ => y0 - (X.cumDemand (X.count t ω) ω : ℤ)) :=
    (measurable_of_countable (fun n : ℕ => y0 - (X.cumDemand n ω : ℤ))).comp hN
  have hlim := p0d2_avg (sPolicyCost D h b1) (fun t : ℝ => y0 - (X.cumDemand (X.count t ω) ω : ℤ))
    hW R Q hQ hUω
  have hval : (∑ k ∈ Finset.range Q, sPolicyCost D h b1 (R + 1 + (k : ℤ))) / (Q : ℝ)
      = windowCost D h b1 Q R / Q := rfl
  rw [hval] at hlim
  exact p0d2_shift (sPolicyCost D h b1)
    (fun s : ℝ => reduceToBand R Q (y0 - (X.cumDemand (X.count s ω) ω : ℤ)))
    ((measurable_of_countable (reduceToBand R Q)).comp hW)
    (∑ k ∈ Finset.range Q, |sPolicyCost D h b1 (R + 1 + (k : ℤ))|)
    (fun s => p0d2_bound (sPolicyCost D h b1) R Q hQ _) y0 L hL _ hlim


open InventoryControl in
lemma p200_band (R : ℤ) (Q : ℕ) (hQ : 0 < Q) (z : ℤ) :
    R + 1 ≤ reduceToBand R Q z ∧ reduceToBand R Q z ≤ R + Q ∧
      (Q : ℤ) ∣ reduceToBand R Q z - z := by
  have hQ' : (0 : ℤ) < Q := by exact_mod_cast hQ
  unfold reduceToBand
  refine ⟨?_, ?_, ?_⟩
  · have := Int.emod_nonneg (z - (R + 1)) hQ'.ne'
    linarith
  · have := Int.emod_lt_of_pos (z - (R + 1)) hQ'
    linarith
  · have h := Int.emod_add_mul_ediv (z - (R + 1)) (Q : ℤ)
    exact ⟨-((z - (R + 1)) / (Q : ℤ)), by linear_combination h⟩

open InventoryControl in
lemma p200_uniq (R : ℤ) (Q : ℕ) (hQ : 0 < Q) (z w : ℤ) (h1 : R + 1 ≤ w) (h2 : w ≤ R + Q)
    (hd : (Q : ℤ) ∣ w - z) : w = reduceToBand R Q z := by
  obtain ⟨b1, b2, b3⟩ := p200_band R Q hQ z
  have hx : (Q : ℤ) ∣ w - reduceToBand R Q z := by
    have := dvd_sub hd b3
    rwa [show w - z - (reduceToBand R Q z - z) = w - reduceToBand R Q z by ring] at this
  have := Int.eq_zero_of_abs_lt_dvd hx (by rw [abs_lt]; constructor <;> linarith)
  linarith

open InventoryControl in
lemma p200_order (R : ℤ) (Q : ℕ) (hQ : 0 < Q) (y : ℤ) :
    y + (Q : ℤ) * ((R + 1 - y + (Q : ℤ) - 1) / (Q : ℤ)) = reduceToBand R Q y := by
  have hQ' : (0 : ℤ) < Q := by exact_mod_cast hQ
  have h := Int.emod_add_mul_ediv (R + 1 - y + (Q : ℤ) - 1) (Q : ℤ)
  have h2 := Int.emod_lt_of_pos (R + 1 - y + (Q : ℤ) - 1) hQ'
  have h3 := Int.emod_nonneg (R + 1 - y + (Q : ℤ) - 1) hQ'.ne'
  apply p200_uniq R Q hQ
  · linarith
  · linarith
  · exact ⟨(R + 1 - y + (Q : ℤ) - 1) / (Q : ℤ), by ring⟩

open InventoryControl in
lemma p200_succ {Ω : Type*} [MeasurableSpace Ω] {P : MeasureTheory.Measure Ω}
    (X : CompoundPoissonDemand P) (R : ℤ) (Q : ℕ) (hQ : 0 < Q) (y0 : ℤ) (n : ℕ) (ω : Ω) :
    rqIP X R Q y0 (n + 1) ω
      = if R + 1 ≤ rqIP X R Q y0 n ω - (X.dem n ω : ℤ) then rqIP X R Q y0 n ω - (X.dem n ω : ℤ)
        else reduceToBand R Q (rqIP X R Q y0 n ω - (X.dem n ω : ℤ)) := by
  simp only [rqIP]
  split_ifs with h
  · rfl
  · exact p200_order R Q hQ _

open InventoryControl in
lemma p200_cum {Ω : Type*} [MeasurableSpace Ω] {P : MeasureTheory.Measure Ω}
    (X : CompoundPoissonDemand P) (n : ℕ) (ω : Ω) :
    (X.cumDemand (n + 1) ω : ℤ) = (X.cumDemand n ω : ℤ) + (X.dem n ω : ℤ) := by
  unfold CompoundPoissonDemand.cumDemand
  rw [Finset.sum_range_succ]
  push_cast
  ring

open InventoryControl in
lemma p200_main {Ω : Type*} [MeasurableSpace Ω] {P : MeasureTheory.Measure Ω}
    (X : CompoundPoissonDemand P) (R : ℤ) (Q : ℕ) (hQ : 0 < Q) (y0 : ℤ) (ω : Ω) (n : ℕ) :
    (0 < n ∨ R + 1 ≤ y0 →
      rqIP X R Q y0 n ω
        = (if R + 1 ≤ y0 - (X.cumDemand n ω : ℤ) then y0 - (X.cumDemand n ω : ℤ)
           else reduceToBand R Q (y0 - (X.cumDemand n ω : ℤ)))) := by
  induction n with
  | zero =>
    intro h
    have hy : R + 1 ≤ y0 := by
      rcases h with h | h
      · omega
      · exact h
    have hS : (X.cumDemand 0 ω : ℤ) = 0 := by simp [CompoundPoissonDemand.cumDemand]
    rw [hS, sub_zero, if_pos hy]
    rfl
  | succ n ih =>
    intro _
    rw [p200_succ X R Q hQ y0 n ω, p200_cum X n ω]
    have hd : (0 : ℤ) ≤ (X.dem n ω : ℤ) := by positivity
    rw [show y0 - ((X.cumDemand n ω : ℤ) + (X.dem n ω : ℤ))
        = (y0 - (X.cumDemand n ω : ℤ)) - (X.dem n ω : ℤ) by ring]
    set z := y0 - (X.cumDemand n ω : ℤ) with hz
    set d := (X.dem n ω : ℤ) with hdd
    by_cases h0 : 0 < n ∨ R + 1 ≤ y0
    · have ih' := ih h0
      by_cases hzR : R + 1 ≤ z
      · rw [ih', if_pos hzR]
      · rw [ih', if_neg hzR]
        have hzd : ¬ R + 1 ≤ z - d := by omega
        rw [if_neg hzd]
        obtain ⟨b1, b2, b3⟩ := p200_band R Q hQ z
        split_ifs with hb
        · apply p200_uniq R Q hQ
          · exact hb
          · linarith
          · rwa [show reduceToBand R Q z - d - (z - d) = reduceToBand R Q z - z by ring]
        · obtain ⟨c1, c2, c3⟩ := p200_band R Q hQ (reduceToBand R Q z - d)
          apply p200_uniq R Q hQ
          · exact c1
          · exact c2
          · have := dvd_add c3 b3
            rwa [show reduceToBand R Q (reduceToBand R Q z - d) - (reduceToBand R Q z - d)
                + (reduceToBand R Q z - z)
                = reduceToBand R Q (reduceToBand R Q z - d) - (z - d) by ring] at this
    · have hn : n = 0 := by omega
      have hy : ¬ R + 1 ≤ y0 := fun h => h0 (Or.inr h)
      subst hn
      have hS : (X.cumDemand 0 ω : ℤ) = 0 := by simp [CompoundPoissonDemand.cumDemand]
      have hr : rqIP X R Q y0 0 ω = z := by
        rw [hz, hS, sub_zero]
        rfl
      rw [hr]

open InventoryControl in
lemma p200_ip {Ω : Type*} [MeasurableSpace Ω] {P : MeasureTheory.Measure Ω}
    (X : CompoundPoissonDemand P) (R : ℤ) (Q : ℕ) (hQ : 0 < Q) (y0 : ℤ) (ω : Ω) (n : ℕ) :
    ipPath X Q y0 (rqOrders X R Q y0) n ω = rqIP X R Q y0 n ω := by
  have hQ' : (0 : ℤ) < Q := by exact_mod_cast hQ
  induction n with
  | zero => rfl
  | succ n ih =>
    have hdiff : ∃ c : ℤ, 0 ≤ c ∧
        rqIP X R Q y0 (n + 1) ω - (rqIP X R Q y0 n ω - (X.dem n ω : ℤ)) = (Q : ℤ) * c := by
      rw [p200_succ X R Q hQ y0 n ω]
      split_ifs with h
      · exact ⟨0, le_refl _, by ring⟩
      · rw [← p200_order R Q hQ]
        refine ⟨(R + 1 - (rqIP X R Q y0 n ω - (X.dem n ω : ℤ)) + (Q : ℤ) - 1) / (Q : ℤ), ?_,
          by ring⟩
        apply Int.ediv_nonneg
        · omega
        · exact hQ'.le
    obtain ⟨c, hc0, hc⟩ := hdiff
    simp only [ipPath]
    rw [ih]
    unfold rqOrders
    rw [hc, Int.mul_ediv_cancel_left c hQ'.ne', Int.toNat_of_nonneg hc0]
    linarith


-- ============ Part F: the (R,Q) position agrees with the reduced one eventually (097324be) ============

lemma p097_absle (g : ℤ → ℝ) (a b z : ℤ) (h1 : a ≤ z) (h2 : z ≤ b) :
    |g z| ≤ ∑ w ∈ Finset.Icc a b, |g w| :=
  Finset.single_le_sum (f := fun w => |g w|) (fun w _ => abs_nonneg (g w))
    (Finset.mem_Icc.2 ⟨h1, h2⟩)

open MeasureTheory Filter Topology in
lemma p097_eventual (F G : ℝ → ℝ) (hF : Measurable F) (hG : Measurable G) (B : ℝ)
    (hFB : ∀ t, |F t| ≤ B) (hGB : ∀ t, |G t| ≤ B) (C : ℝ) (hC : ∀ t, C ≤ t → F t = G t)
    (ℓ : ℝ) (hlim : Tendsto (fun T : ℝ => (1 / T) * ∫ t in (0:ℝ)..T, G t) atTop (𝓝 ℓ)) :
    Tendsto (fun T : ℝ => (1 / T) * ∫ t in (0:ℝ)..T, F t) atTop (𝓝 ℓ) := by
  have hFi : ∀ a b : ℝ, IntervalIntegrable F volume a b := p0d2_ii F hF B hFB
  have hGi : ∀ a b : ℝ, IntervalIntegrable G volume a b := p0d2_ii G hG B hGB
  set K : ℝ := ∫ t in (0:ℝ)..C, (F t - G t) with hK
  have heq : ∀ T : ℝ, C ≤ T → ∫ t in (0:ℝ)..T, F t = (∫ t in (0:ℝ)..T, G t) + K := by
    intro T hCT
    have hsub : ∫ t in (0:ℝ)..T, (F t - G t)
        = (∫ t in (0:ℝ)..T, F t) - ∫ t in (0:ℝ)..T, G t :=
      intervalIntegral.integral_sub (hFi 0 T) (hGi 0 T)
    have hsplit := intervalIntegral.integral_add_adjacent_intervals
      ((hFi 0 C).sub (hGi 0 C)) ((hFi C T).sub (hGi C T))
    have hzero : ∫ t in C..T, (F t - G t) = 0 := by
      rw [intervalIntegral.integral_congr (g := fun _ => (0:ℝ)) ?_]
      · simp
      · intro t ht
        rw [Set.uIcc_of_le hCT] at ht
        simp only [hC t ht.1, sub_self]
    rw [hzero, add_zero, hsub] at hsplit
    have hK' : K = (∫ t in (0:ℝ)..T, F t) - ∫ t in (0:ℝ)..T, G t := by rw [hK]; exact hsplit
    rw [hK']
    ring
  have h3 : Tendsto (fun T : ℝ => K * T⁻¹) atTop (𝓝 (K * 0)) :=
    tendsto_const_nhds.mul tendsto_inv_atTop_zero
  have hc := hlim.add h3
  rw [mul_zero, add_zero] at hc
  refine hc.congr' ?_
  filter_upwards [eventually_ge_atTop C] with T hT
  rw [heq T hT]
  ring

open InventoryControl in
lemma p097_rq_range {Ω : Type*} [MeasurableSpace Ω] {P : MeasureTheory.Measure Ω}
    (X : CompoundPoissonDemand P) (R : ℤ) (Q : ℕ) (hQ : 0 < Q) (y0 : ℤ) (ω : Ω) (n : ℕ) :
    min (R + 1) y0 ≤ rqIP X R Q y0 n ω ∧ rqIP X R Q y0 n ω ≤ max (R + Q) y0 := by
  rcases Nat.eq_zero_or_pos n with h0 | hpos
  · subst h0
    have : rqIP X R Q y0 0 ω = y0 := rfl
    rw [this]
    exact ⟨min_le_right _ _, le_max_right _ _⟩
  · rw [p200_main X R Q hQ y0 ω n (Or.inl hpos)]
    have hS : (0 : ℤ) ≤ (X.cumDemand n ω : ℤ) := by positivity
    split_ifs with hc
    · constructor
      · exact le_trans (min_le_left _ _) hc
      · exact le_trans (by linarith) (le_max_right _ _)
    · obtain ⟨b1, b2, _⟩ := p200_band R Q hQ (y0 - (X.cumDemand n ω : ℤ))
      exact ⟨le_trans (min_le_left _ _) b1, le_trans b2 (le_max_left _ _)⟩

open InventoryControl in
lemma p097_rq_eq {Ω : Type*} [MeasurableSpace Ω] {P : MeasureTheory.Measure Ω}
    (X : CompoundPoissonDemand P) (R : ℤ) (Q : ℕ) (hQ : 0 < Q) (y0 : ℤ) (ω : Ω)
    (hd : ∀ n, 1 ≤ X.dem n ω) (n : ℕ) (hn : max 1 (y0 - R - Q).toNat ≤ n) :
    rqIP X R Q y0 n ω = reduceToBand R Q (y0 - (X.cumDemand n ω : ℤ)) := by
  have hQ' : (0 : ℤ) < Q := by exact_mod_cast hQ
  have hpos : 0 < n := lt_of_lt_of_le (by norm_num) (le_trans (le_max_left _ _) hn)
  have hSn : n ≤ X.cumDemand n ω := by
    unfold CompoundPoissonDemand.cumDemand
    calc n = ∑ _i ∈ Finset.range n, 1 := by simp
      _ ≤ ∑ i ∈ Finset.range n, X.dem i ω := Finset.sum_le_sum fun i _ => hd i
  have hn2 : (y0 - R - Q).toNat ≤ n := le_trans (le_max_right _ _) hn
  have hS : y0 - R - Q ≤ (X.cumDemand n ω : ℤ) := by
    have h1 : y0 - R - Q ≤ ((y0 - R - Q).toNat : ℤ) := Int.self_le_toNat _
    have h2 : (((y0 - R - Q).toNat : ℕ) : ℤ) ≤ (n : ℤ) := by exact_mod_cast hn2
    have h3 : (n : ℤ) ≤ (X.cumDemand n ω : ℤ) := by exact_mod_cast hSn
    linarith
  rw [p200_main X R Q hQ y0 ω n (Or.inl hpos)]
  split_ifs with hc
  · unfold reduceToBand
    rw [Int.emod_eq_of_lt (by linarith) (by linarith)]
    ring
  · rfl

open InventoryControl in
lemma p097_count_ge {Ω : Type*} [MeasurableSpace Ω] {P : MeasureTheory.Measure Ω}
    (X : CompoundPoissonDemand P) (ω : Ω) (hg : ∀ n, 0 < X.gap n ω)
    (hinf : Filter.Tendsto (fun n => X.arrival n ω) Filter.atTop Filter.atTop) (N : ℕ) (s : ℝ)
    (hs : X.arrival N ω ≤ s) : N ≤ X.count s ω := by
  have h0 : 0 ≤ X.arrival N ω := by
    unfold CompoundPoissonDemand.arrival
    exact Finset.sum_nonneg fun i _ => (hg i).le
  obtain ⟨_, h2⟩ := p0d2_count_bracket X ω hg hinf s (le_trans h0 hs)
  by_contra hlt
  push_neg at hlt
  have := p0d2_arr_mono X ω hg (X.count s ω + 1) N hlt
  linarith

open MeasureTheory ProbabilityTheory Filter Topology InventoryControl in
theorem solution {Ω : Type*} [MeasurableSpace Ω] {P : MeasureTheory.Measure Ω}
    [MeasureTheory.IsProbabilityMeasure P] (X : CompoundPoissonDemand P) (D : DiscreteDemand)
    (h b1 L : ℝ) (hh : 0 < h) (hb : 0 < b1) (hL : 0 ≤ L)
    (hD : ∀ j : ℕ, D.p j = P.real {ω | X.cumDemand (X.count L ω) ω = j})
    (Q : ℕ) (hQ : 0 < Q) (R : ℤ) (y0 : ℤ) :
    ∀ᵐ ω ∂P, Filter.Tendsto (fun T => avgCost X D h b1 L Q y0 (rqOrders X R Q y0) T ω)
      Filter.atTop (nhds (windowCost D h b1 Q R / Q)) := by
  filter_upwards [p097_reduced X D h b1 L hL R Q hQ y0, p0d2_gap_pos X, p0d2_gap_slln X,
    p0d2_dem_pos X] with ω hlim hg hG hd
  have hinf := p0d2_arr_tendsto X ω (p0d2_mu X) (p0d2_mu_pos X) hG
  have hN : Measurable (fun t => X.count t ω) := (p0d2_count_mono X ω hg hinf).measurable
  set g : ℤ → ℝ := sPolicyCost D h b1 with hgdef
  set a : ℤ := min (R + 1) y0 with ha
  set bb : ℤ := max (R + Q) y0 with hbb
  set B : ℝ := ∑ w ∈ Finset.Icc a bb, |g w| with hB
  set V1 : ℝ → ℤ := fun t => if t < L then y0 else rqIP X R Q y0 (X.count (t - L) ω) ω with hV1
  set V2 : ℝ → ℤ := fun t => if t < L then y0
    else reduceToBand R Q (y0 - (X.cumDemand (X.count (t - L) ω) ω : ℤ)) with hV2
  have hV1m : Measurable V1 :=
    Measurable.ite measurableSet_Iio measurable_const
      ((measurable_of_countable (fun n : ℕ => rqIP X R Q y0 n ω)).comp
        (hN.comp (measurable_id.sub_const L)))
  have hV2m : Measurable V2 :=
    Measurable.ite measurableSet_Iio measurable_const
      ((measurable_of_countable
        (fun n : ℕ => reduceToBand R Q (y0 - (X.cumDemand n ω : ℤ)))).comp
        (hN.comp (measurable_id.sub_const L)))
  have hy0 : a ≤ y0 ∧ y0 ≤ bb := ⟨min_le_right _ _, le_max_right _ _⟩
  have hV1b : ∀ t, |g (V1 t)| ≤ B := by
    intro t
    simp only [hV1]
    split_ifs
    · exact p097_absle g a bb y0 hy0.1 hy0.2
    · obtain ⟨r1, r2⟩ := p097_rq_range X R Q hQ y0 ω (X.count (t - L) ω)
      exact p097_absle g a bb _ r1 r2
  have hV2b : ∀ t, |g (V2 t)| ≤ B := by
    intro t
    simp only [hV2]
    split_ifs
    · exact p097_absle g a bb y0 hy0.1 hy0.2
    · obtain ⟨b1', b2', _⟩ := p200_band R Q hQ (y0 - (X.cumDemand (X.count (t - L) ω) ω : ℤ))
      exact p097_absle g a bb _ (le_trans (min_le_left _ _) b1') (le_trans b2' (le_max_left _ _))
  set N : ℕ := max 1 (y0 - R - Q).toNat with hNdef
  have hC : ∀ t, L + X.arrival N ω ≤ t → g (V1 t) = g (V2 t) := by
    intro t ht
    have hA : 0 ≤ X.arrival N ω := by
      unfold CompoundPoissonDemand.arrival
      exact Finset.sum_nonneg fun i _ => (hg i).le
    have htL : ¬ t < L := by linarith
    simp only [hV1, hV2, if_neg htL]
    have hcnt : N ≤ X.count (t - L) ω :=
      p097_count_ge X ω hg hinf N (t - L) (by linarith)
    rw [p097_rq_eq X R Q hQ y0 ω hd _ hcnt]
  have hmain := p097_eventual (fun t => g (V1 t)) (fun t => g (V2 t))
    ((measurable_of_countable g).comp hV1m) ((measurable_of_countable g).comp hV2m) B hV1b hV2b
    (L + X.arrival N ω) hC _ hlim
  refine hmain.congr fun T => ?_
  unfold avgCost
  congr 1
  refine intervalIntegral.integral_congr fun t _ => ?_
  simp only [hV1, ipAt, p200_ip X R Q hQ y0 ω]
  rfl
