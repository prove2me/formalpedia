-- Prove2me | solution 1 for ImperfReport.Regulator.proposition_1
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-26T09:59:07.436375+00:00
-- url     : https://prove2.me/submissions/8468c793-4952-4735-89f0-f10cdba43713

import Mathlib
import Definitions.Def_ImperfReport_Regulator_Variance

set_option autoImplicit false
open MeasureTheory Set

namespace ImperfReport.Regulator

/-- the call-option integral `∫ max (t - x) 0 dμ` -/
noncomputable def p1h (M : Model) (t : ℝ) : ℝ := ∫ x, max (t - x) 0 ∂M.mu

section P1
variable {M : Model} (hM : M.Standing)
include hM

lemma p1_prob : IsProbabilityMeasure M.mu := hM.2.2.2.2.1

lemma p1_noatoms : NullSingletonClass M.mu := hM.2.2.2.2.2.2.1

lemma p1_ae01 : ∀ᵐ x ∂M.mu, x ∈ Icc (0:ℝ) 1 := ae_iff.2 hM.2.2.2.2.2.1

lemma p1_null_of_sub {s : Set ℝ} (hs : s ⊆ (Icc (0:ℝ) 1)ᶜ) : M.mu s = 0 :=
  measure_mono_null hs hM.2.2.2.2.2.1

lemma p1_int_bdd {f : ℝ → ℝ} (hf : Continuous f) (C : ℝ)
    (hC : ∀ x ∈ Icc (0:ℝ) 1, |f x| ≤ C) : Integrable f M.mu := by
  haveI := p1_prob hM
  refine Integrable.of_bound hf.aestronglyMeasurable C ?_
  filter_upwards [p1_ae01 hM] with x hx
  simpa [Real.norm_eq_abs] using hC x hx

lemma p1_int_id : Integrable (fun x : ℝ => x) M.mu :=
  p1_int_bdd hM continuous_id 1 (fun x hx => by
    rw [abs_le]; constructor <;> linarith [hx.1, hx.2])

lemma p1_int_sq : Integrable (fun x : ℝ => x ^ 2) M.mu :=
  p1_int_bdd hM (continuous_pow 2) 1 (fun x hx => by
    rw [abs_le]; constructor <;> nlinarith [hx.1, hx.2])

lemma p1_int_max (t : ℝ) : Integrable (fun x : ℝ => max (t - x) 0) M.mu :=
  p1_int_bdd hM (by fun_prop) (|t| + 1) (fun x hx => by
    rw [abs_le]; constructor
    · nlinarith [le_max_right (t - x) 0, abs_nonneg t]
    · rcases le_total (t - x) 0 with h | h
      · rw [max_eq_right h]; linarith [abs_nonneg t]
      · rw [max_eq_left h]; linarith [le_abs_self t, hx.1])

lemma p1_beta_le : beta M ≤ 1 := by
  haveI := p1_prob hM
  have h : ∫ x, x ∂M.mu ≤ ∫ _x, (1:ℝ) ∂M.mu :=
    integral_mono_ae (p1_int_id hM) (integrable_const 1)
      (by filter_upwards [p1_ae01 hM] with x hx using hx.2)
  simpa [beta] using h

lemma p1_Ioi (t : ℝ) : M.mu.real (Ioi t) = 1 - F M t := by
  haveI := p1_prob hM
  rw [← compl_Iic, measureReal_compl measurableSet_Iic]; simp [F]

lemma p1_F_Iio (y : ℝ) : F M y = M.mu.real (Iio y) := by
  haveI := p1_noatoms hM
  simp only [F, measureReal_def, measure_congr (Iio_ae_eq_Iic (μ := M.mu) (a := y))]

/-- the partial first moment in terms of the call integral -/
lemma p1_Iic_int (t : ℝ) :
    ∫ x in Iic t, x ∂M.mu = t * F M t - p1h M t := by
  haveI := p1_prob hM
  have h1 : p1h M t = ∫ x in Iic t, (t - x) ∂M.mu := by
    rw [p1h, ← integral_indicator measurableSet_Iic]
    congr 1; funext x
    by_cases hx : x ≤ t
    · rw [indicator_of_mem (show x ∈ Iic t from hx), max_eq_left (by linarith)]
    · rw [indicator_of_notMem (show x ∉ Iic t from hx), max_eq_right (by push_neg at hx; linarith)]
  rw [h1, integral_sub (integrable_const t).integrableOn (p1_int_id hM).integrableOn,
    setIntegral_const, F, smul_eq_mul]
  ring

lemma p1_cut_iff (q t : ℝ) :
    IsCutoff M q t ↔ t ∈ Icc (0:ℝ) 1 ∧ (1 - q) * (beta M - t) = q * p1h M t := by
  unfold IsCutoff
  rw [p1_Iic_int hM]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨h1, by linear_combination h2⟩
  · rintro ⟨h1, h2⟩; exact ⟨h1, by linear_combination h2⟩

lemma p1_h_mono {t t' : ℝ} (htt : t ≤ t') : p1h M t ≤ p1h M t' :=
  integral_mono (p1_int_max hM t) (p1_int_max hM t')
    (fun x => max_le_max (by linarith) le_rfl)

lemma p1_h_pos {k : ℝ} (hk : 0 < k) (hk1 : k ≤ 1) : 0 < p1h M k := by
  haveI := p1_prob hM
  unfold p1h
  rw [integral_pos_iff_support_of_nonneg
    (show (0 : ℝ → ℝ) ≤ fun x => max (k - x) 0 from fun x => le_max_right _ _) (p1_int_max hM k)]
  have hpos := hM.2.2.2.2.2.2.2 0 k le_rfl hk hk1
  refine lt_of_lt_of_le hpos (measure_mono ?_)
  intro x hx
  exact (lt_max_of_lt_left (sub_pos.2 hx.2)).ne'

lemma p1_h_zero : p1h M 0 = 0 := by
  unfold p1h
  apply integral_eq_zero_of_ae
  filter_upwards [p1_ae01 hM] with x hx
  simp only [Pi.zero_apply]
  exact max_eq_right (by linarith [hx.1])

/-- layer cake: the integral of the CDF is the call integral -/
lemma p1_layer {k : ℝ} (hk : 0 ≤ k) : ∫ x in (0)..k, F M x = p1h M k := by
  haveI := p1_prob hM
  have hL := Integrable.integral_eq_integral_meas_lt (p1_int_max hM k)
    (Filter.Eventually.of_forall (fun x => le_max_right (k - x) 0))
  unfold p1h
  rw [hL]
  have h2 : ∫ t in Ioi (0:ℝ), M.mu.real {a : ℝ | t < max (k - a) 0} =
      ∫ t in Ioi (0:ℝ), M.mu.real (Iio (k - t)) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    simp only
    congr 1
    ext a
    simp only [mem_setOf_eq, mem_Iio, lt_max_iff]
    constructor
    · rintro (h | h)
      · linarith
      · exact absurd h (not_lt.2 (le_of_lt ht))
    · intro h; left; linarith
  rw [h2]
  have h3 : ∫ t in Ioi (0:ℝ), M.mu.real (Iio (k - t)) =
      ∫ t in Ioc (0:ℝ) k, M.mu.real (Iio (k - t)) := by
    apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi Ioc_subset_Ioi_self
    intro t ht
    have htk : k < t := by
      by_contra hcon
      exact ht.2 ⟨ht.1, not_lt.1 hcon⟩
    rw [measureReal_def, p1_null_of_sub hM (s := Iio (k - t)) (by
      intro y hy hy01
      have : y < k - t := hy
      linarith [hy01.1])]
    simp
  rw [h3, ← intervalIntegral.integral_of_le hk]
  have h4 : (fun t => M.mu.real (Iio (k - t))) = fun t => F M (k - t) := by
    funext t; rw [p1_F_Iio hM]
  rw [h4, intervalIntegral.integral_comp_sub_left (fun x => F M x) k]
  simp

lemma p1_tdag_nonneg (q : ℝ) : 0 ≤ tdag M q :=
  Real.sInf_nonneg (fun _ ht => ht.1.1)

lemma p1_bdd (q : ℝ) : BddBelow {t : ℝ | IsCutoff M q t} :=
  ⟨0, fun _ ht => ht.1.1⟩

lemma p1_tdag_one : tdag M 1 = 0 := by
  have h0 : IsCutoff M 1 0 := by
    rw [p1_cut_iff hM, p1_h_zero hM]
    exact ⟨⟨le_rfl, zero_le_one⟩, by ring⟩
  exact le_antisymm (csInf_le (p1_bdd hM 1) h0) (p1_tdag_nonneg hM 1)

lemma p1_Ioi_zero_ae : ∀ᵐ x ∂M.mu, x ∈ Ioi (0:ℝ) := by
  haveI := p1_noatoms hM
  have hne : ∀ᵐ x ∂M.mu, x ≠ 0 := by
    apply ae_iff.2
    have : {a : ℝ | ¬a ≠ 0} = {0} := by ext a; simp
    rw [this]; exact measure_singleton 0
  filter_upwards [p1_ae01 hM, hne] with x h1 h2
  exact lt_of_le_of_ne h1.1 (Ne.symm h2)

lemma p1_restrict_Ioi0 : M.mu.restrict (Ioi (0:ℝ)) = M.mu :=
  Measure.restrict_eq_self_of_ae_mem (p1_Ioi_zero_ae hM)

/-- data at the perfect-report best response -/
lemma p1_q0_facts (hk0 : 0 < M.k) (hkb : M.k < beta M) :
    0 < qdag M M.k ∧ qdag M M.k < 1 ∧
    (1 - qdag M M.k) * (beta M - M.k) = qdag M M.k * p1h M M.k := by
  have hk1 : M.k ≤ 1 := by linarith [p1_beta_le hM]
  have hH := p1_h_pos hM hk0 hk1
  have hB : 0 < beta M - M.k := by linarith
  unfold qdag
  rw [p1_layer hM hk0.le]
  refine ⟨div_pos hB (by linarith), (div_lt_one (by linarith)).2 (by linarith), ?_⟩
  field_simp
  ring

lemma p1_tdag_q0 (hk0 : 0 < M.k) (hkb : M.k < beta M) : tdag M (qdag M M.k) = M.k := by
  obtain ⟨hq0, hq1, heq⟩ := p1_q0_facts hM hk0 hkb
  have hk1 : M.k ≤ 1 := by linarith [p1_beta_le hM]
  have hk : IsCutoff M (qdag M M.k) M.k := by
    rw [p1_cut_iff hM]; exact ⟨⟨hk0.le, hk1⟩, heq⟩
  apply le_antisymm (csInf_le (p1_bdd hM _) hk)
  apply le_csInf ⟨M.k, hk⟩
  intro t ht
  rw [mem_setOf_eq, p1_cut_iff hM] at ht
  by_contra hlt
  push_neg at hlt
  have hm := p1_h_mono hM hlt.le
  have : (1 - qdag M M.k) * (beta M - M.k) < (1 - qdag M M.k) * (beta M - t) :=
    mul_lt_mul_of_pos_left (by linarith) (by linarith)
  nlinarith [ht.2]

lemma p1_tdag_gt (hk0 : 0 < M.k) (hkb : M.k < beta M) {q : ℝ}
    (hq : qdag M M.k < q) (hq1 : q ≤ 1) : tdag M q < M.k := by
  obtain ⟨hq0, hq01, heq⟩ := p1_q0_facts hM hk0 hkb
  have hk1 : M.k ≤ 1 := by linarith [p1_beta_le hM]
  have hH := p1_h_pos hM hk0 hk1
  have hall : ∀ t, IsCutoff M q t → t < M.k := by
    intro t ht
    rw [p1_cut_iff hM] at ht
    by_contra hge
    push_neg at hge
    have hm := p1_h_mono hM hge
    have e1 : (1 - q) * (beta M - t) ≤ (1 - q) * (beta M - M.k) :=
      mul_le_mul_of_nonneg_left (by linarith) (by linarith)
    have e2 : q * p1h M M.k ≤ q * p1h M t :=
      mul_le_mul_of_nonneg_left hm (by linarith)
    nlinarith [ht.2]
  by_cases hne : ({t : ℝ | IsCutoff M q t}).Nonempty
  · obtain ⟨t, ht⟩ := hne
    exact lt_of_le_of_lt (csInf_le (p1_bdd hM q) ht) (hall t ht)
  · rw [not_nonempty_iff_eq_empty] at hne
    unfold tdag; rw [hne, Real.sInf_empty]; exact hk0

lemma p1_succ_one (q : ℝ) (hk1 : M.k ≤ 1) : succ M 1 q = 1 := by
  haveI := p1_prob hM
  have ht := p1_tdag_nonneg hM q
  unfold succ
  simp only
  have hs : {s : ℝ | tdag M q < s ∧ M.k ≤ 1 + s} = Ioi (tdag M q) := by
    ext s; simp only [mem_setOf_eq, mem_Ioi]
    constructor
    · exact fun h => h.1
    · intro h; exact ⟨h, by linarith⟩
  rw [hs, if_pos (by linarith)]
  ring

lemma p1_succ_k (q : ℝ) : succ M M.k q = 1 := by
  have ht := p1_tdag_nonneg hM q
  unfold succ
  simp only
  have hs : {s : ℝ | tdag M q < s ∧ M.k ≤ M.k + s} = Ioi (tdag M q) := by
    ext s; simp only [mem_setOf_eq, mem_Ioi]
    constructor
    · exact fun h => h.1
    · intro h; exact ⟨h, by linarith⟩
  rw [hs, if_pos (by linarith)]
  ring

lemma p1_succ_le_one (a q : ℝ) (hq : q ∈ Icc (0:ℝ) 1) : succ M a q ≤ 1 := by
  haveI := p1_prob hM
  unfold succ
  simp only
  have hsub : {s : ℝ | tdag M q < s ∧ M.k ≤ a + s} ⊆ Ioi (tdag M q) := fun s hs => hs.1
  have hA := measureReal_mono (μ := M.mu) hsub
  have hA0 : 0 ≤ M.mu.real {s : ℝ | tdag M q < s ∧ M.k ≤ a + s} := measureReal_nonneg
  have hA1 : M.mu.real {s : ℝ | tdag M q < s ∧ M.k ≤ a + s} ≤ 1 := measureReal_le_one
  have hI1 : M.mu.real (Ioi (tdag M q)) ≤ 1 := measureReal_le_one
  split_ifs
  · nlinarith [hq.1]
  · nlinarith [hq.1, hq.2]

lemma p1_pG_perfect : pG M perfect = M.alpha := by
  simp [pG, perfect]

lemma p1_pass_perfect (q : ℝ) (hk1 : M.k ≤ 1) :
    pass M perfect q = M.alpha + (1 - M.alpha) * succ M 0 q := by
  unfold pass
  rw [p1_pG_perfect hM]
  simp only [perfect]
  rw [p1_succ_one hM q hk1]
  ring

lemma p1_FirmBR_perfect (hk0 : 0 < M.k) (hkb : M.k < beta M) :
    FirmBR M perfect (qdag M M.k) := by
  haveI := p1_prob hM
  obtain ⟨hq0, hq1, heq⟩ := p1_q0_facts hM hk0 hkb
  have hk1 : M.k ≤ 1 := by linarith [p1_beta_le hM]
  have ha1 : M.alpha < 1 := hM.2.1
  have hpass0 : pass M perfect (qdag M M.k) = 1 := by
    rw [p1_pass_perfect hM _ hk1]
    have : succ M 0 (qdag M M.k) = 1 := by
      unfold succ; simp only
      rw [p1_tdag_q0 hM hk0 hkb]
      have hs : {s : ℝ | M.k < s ∧ M.k ≤ 0 + s} = Ioi M.k := by
        ext s; simp only [mem_setOf_eq, mem_Ioi]
        constructor
        · exact fun h => h.1
        · intro h; exact ⟨h, by linarith⟩
      rw [hs, if_pos (by linarith)]; ring
    rw [this]; ring
  have hle : ∀ q ∈ Icc (0:ℝ) 1, pass M perfect q ≤ 1 := by
    intro q hq
    rw [p1_pass_perfect hM _ hk1]
    have := p1_succ_le_one hM 0 q hq
    nlinarith
  refine ⟨⟨hq0.le, hq1.le⟩, fun q hq => by rw [hpass0]; exact hle q hq, ?_⟩
  intro q hq hpq
  by_contra hlt
  push_neg at hlt
  have htq := p1_tdag_gt hM hk0 hkb hlt hq.2
  have hsucc : succ M 0 q < 1 := by
    unfold succ; simp only
    have hs : {s : ℝ | tdag M q < s ∧ M.k ≤ 0 + s} = Ici M.k := by
      ext s; simp only [mem_setOf_eq, mem_Ici]
      constructor
      · intro h; linarith [h.2]
      · intro h; exact ⟨by linarith, by linarith⟩
    rw [hs, if_neg (by linarith)]
    have hIio : 0 < M.mu.real (Iio M.k) := by
      rw [measureReal_def]
      apply ENNReal.toReal_pos
      · exact (lt_of_lt_of_le (hM.2.2.2.2.2.2.2 0 M.k le_rfl hk0 hk1)
          (measure_mono Ioo_subset_Iio_self)).ne'
      · exact measure_ne_top _ _
    have hIci : M.mu.real (Ici M.k) = 1 - M.mu.real (Iio M.k) := by
      rw [← compl_Iio, measureReal_compl measurableSet_Iio]; simp
    rw [hIci]
    nlinarith [hq.2, hq.1]
  rw [hpass0, p1_pass_perfect hM _ hk1] at hpq
  nlinarith

lemma p1_pass_rk (q : ℝ) (hk1 : M.k ≤ 1) : pass M (rk M) q = 1 := by
  unfold pass
  simp only [rk]
  rw [p1_succ_one hM q hk1, p1_succ_k hM q]
  ring

lemma p1_FirmBR_rk (hk1 : M.k ≤ 1) : FirmBR M (rk M) 1 := by
  refine ⟨⟨zero_le_one, le_rfl⟩, fun q _ => by rw [p1_pass_rk hM q hk1, p1_pass_rk hM 1 hk1], ?_⟩
  intro q hq _; exact hq.2

lemma p1_FirmBR_unique {r : Report} {q q' : ℝ} (h : FirmBR M r q) (h' : FirmBR M r q') :
    q = q' := by
  have e1 := h.2.1 q' h'.1
  have e2 := h'.2.1 q h.1
  have e : pass M r q' = pass M r q := le_antisymm e1 e2
  exact le_antisymm (h'.2.2 q h.1 e.symm) (h.2.2 q' h'.1 e)

lemma p1_EM_one : EM M 1 = beta M := by
  unfold EM; simp only
  rw [p1_tdag_one hM, p1_restrict_Ioi0 hM]
  simp [beta]

lemma p1_EM2_one : EM2 M 1 = m2 M := by
  unfold EM2; simp only
  rw [p1_tdag_one hM, p1_restrict_Ioi0 hM]
  simp [m2]

lemma p1_Psi_rk (hk1 : M.k < 1) : Psi M (rk M) 1 = M.k * (1 - M.alpha) := by
  unfold Psi Ew2
  rw [p1_EM_one hM, p1_EM2_one hM]
  have hp : pG M (rk M) * (1 - M.k) = M.alpha - M.k := by
    have hne : 1 - M.k ≠ 0 := by linarith
    unfold pG; simp only [rk]
    rw [div_mul_cancel₀ _ hne]
  simp only [rk] at hp ⊢
  linear_combination (-(1 + M.k) - 2 * beta M) * hp

/-- the moment identity: `∫_{Ioi t} f = ∫ f - ∫_{Iic t} f` -/
lemma p1_Ioi_split {f : ℝ → ℝ} (hf : Integrable f M.mu) (t : ℝ) :
    ∫ x in Ioi t, f x ∂M.mu = ∫ x, f x ∂M.mu - ∫ x in Iic t, f x ∂M.mu := by
  have := integral_add_compl (μ := M.mu) (measurableSet_Iic (a := t)) hf
  rw [compl_Iic] at this
  linarith

lemma p1_EM_q0 (hk0 : 0 < M.k) (hkb : M.k < beta M) : EM M (qdag M M.k) = beta M := by
  obtain ⟨_, _, heq⟩ := p1_q0_facts hM hk0 hkb
  unfold EM; simp only
  rw [p1_tdag_q0 hM hk0 hkb, p1_Ioi_split hM (p1_int_id hM), p1_Iic_int hM, p1_Ioi hM]
  have hb : ∫ x, x ∂M.mu = beta M := rfl
  rw [hb]
  linear_combination (-1 : ℝ) * heq

lemma p1_Psi_perfect (hk0 : 0 < M.k) (hkb : M.k < beta M) :
    Psi M perfect (qdag M M.k) = m2 M - EM2 M (qdag M M.k) := by
  unfold Psi Ew2
  rw [p1_pG_perfect hM, p1_EM_q0 hM hk0 hkb]
  simp only [perfect]
  ring

lemma p1_Ioc_eq_Ioi (k : ℝ) :
    ∫ x in Ioc k 1, x ^ 2 ∂M.mu = ∫ x in Ioi k, x ^ 2 ∂M.mu := by
  symm
  apply setIntegral_eq_of_subset_of_ae_sdiff_eq_zero measurableSet_Ioi.nullMeasurableSet
    Ioc_subset_Ioi_self
  filter_upwards [p1_ae01 hM] with x hx hxd
  exact absurd ⟨hxd.1, hx.2⟩ hxd.2

/-- `V ≤ k P`: second moment of nondisclosure mass is at most its first moment -/
lemma p1_V_le (hk0 : 0 < M.k) (hkb : M.k < beta M) :
    m2 M - qdag M M.k * ∫ x in Ioi M.k, x ^ 2 ∂M.mu ≤
      M.k * (1 - qdag M M.k * M.mu.real (Ioi M.k)) := by
  obtain ⟨hq0, hq1, heq⟩ := p1_q0_facts hM hk0 hkb
  have hEM := p1_EM_q0 hM hk0 hkb
  unfold EM at hEM; simp only at hEM
  rw [p1_tdag_q0 hM hk0 hkb] at hEM
  have a1 : ∫ x in Iic M.k, x ^ 2 ∂M.mu ≤ ∫ x in Iic M.k, x ∂M.mu :=
    setIntegral_mono_ae (p1_int_sq hM).integrableOn (p1_int_id hM).integrableOn
      (by filter_upwards [p1_ae01 hM] with x hx; nlinarith [hx.1, hx.2])
  have a2 : ∫ x in Ioi M.k, x ^ 2 ∂M.mu ≤ ∫ x in Ioi M.k, x ∂M.mu :=
    setIntegral_mono_ae (p1_int_sq hM).integrableOn (p1_int_id hM).integrableOn
      (by filter_upwards [p1_ae01 hM] with x hx; nlinarith [hx.1, hx.2])
  have s1 := p1_Ioi_split hM (p1_int_sq hM) M.k
  have s2 := p1_Ioi_split hM (p1_int_id hM) M.k
  have hm2 : m2 M = ∫ x, x ^ 2 ∂M.mu := rfl
  have hb : beta M = ∫ x, x ∂M.mu := rfl
  nlinarith [mul_le_mul_of_nonneg_left a2 (by linarith : (0:ℝ) ≤ 1 - qdag M M.k)]

lemma p1_kalphaO (hk0 : 0 < M.k) :
    M.k * alphaO M = M.k + M.k ^ 2 * (1 - qdag M M.k * M.mu.real (Ioi M.k)) -
      (m2 M - qdag M M.k * ∫ x in Ioi M.k, x ^ 2 ∂M.mu) := by
  unfold alphaO
  rw [p1_Ioi hM, p1_Ioc_eq_Ioi hM]
  field_simp

lemma p1_k_le_alphaO (hk0 : 0 < M.k) (hkb : M.k < beta M) : M.k ≤ alphaO M := by
  have hk1 : M.k ≤ 1 := by linarith [p1_beta_le hM]
  obtain ⟨hq0, hq1, _⟩ := p1_q0_facts hM hk0 hkb
  haveI := p1_prob hM
  have hI1 : M.mu.real (Ioi M.k) ≤ 1 := measureReal_le_one
  have hI0 : 0 ≤ M.mu.real (Ioi M.k) := measureReal_nonneg
  have hV := p1_V_le hM hk0 hkb
  have hK := p1_kalphaO hM hk0
  have hP : 0 ≤ 1 - (1 - qdag M M.k * M.mu.real (Ioi M.k)) := by nlinarith
  have : M.k * M.k ≤ M.k * alphaO M := by
    rw [hK]
    nlinarith [mul_nonneg (mul_nonneg hk0.le (by linarith : (0:ℝ) ≤ 1 - M.k)) hP]
  exact le_of_mul_le_mul_left this hk0

end P1

end ImperfReport.Regulator

open ImperfReport.Regulator in
theorem solution (M : Model) (hM : M.Standing)
    (hk0 : 0 < M.k) (hkb : M.k < beta M) (hα : alphaO M < M.alpha) :
    (rk M).Valid M ∧
    (∃ q, FirmBR M perfect q) ∧
    (∃ q, FirmBR M (rk M) q) ∧
    (∀ q q', FirmBR M perfect q → FirmBR M (rk M) q' →
      Psi M (rk M) q' < Psi M perfect q) ∧
    (∀ (r : Report) (q : ℝ), RegOpt M r q → r.aG = 1 → 0 < r.aB) := by
  have hk1 : M.k < 1 := lt_of_lt_of_le hkb (p1_beta_le hM)
  have hkα : M.k < M.alpha := lt_of_le_of_lt (p1_k_le_alphaO hM hk0 hkb) hα
  have hvalid : (rk M).Valid M :=
    ⟨hk0.le, hkα.le, hM.2.1.le, le_rfl, hk1⟩
  have hBRp := p1_FirmBR_perfect hM hk0 hkb
  have hBRk := p1_FirmBR_rk hM hk1.le
  have hstrict : Psi M (rk M) 1 < Psi M perfect (qdag M M.k) := by
    rw [p1_Psi_rk hM hk1, p1_Psi_perfect hM hk0 hkb]
    have hK := p1_kalphaO hM hk0
    have hmul : M.k * alphaO M < M.k * M.alpha := mul_lt_mul_of_pos_left hα hk0
    unfold EM2; simp only
    rw [p1_tdag_q0 hM hk0 hkb]
    nlinarith
  have hcmp : ∀ q q', FirmBR M perfect q → FirmBR M (rk M) q' →
      Psi M (rk M) q' < Psi M perfect q := by
    intro q q' hq hq'
    rw [p1_FirmBR_unique hM hq hBRp, p1_FirmBR_unique hM hq' hBRk]
    exact hstrict
  refine ⟨hvalid, ⟨_, hBRp⟩, ⟨_, hBRk⟩, hcmp, ?_⟩
  intro r q hr hG
  obtain ⟨hrv, hrbr, hropt⟩ := hr
  by_contra hB
  push_neg at hB
  have hB0 : r.aB = 0 := le_antisymm hB hrv.1
  have hr : r = perfect := by
    cases r; simp only at hG hB0; subst hG; subst hB0; rfl
  subst hr
  have h1 := hropt (rk M) 1 hvalid hBRk
  have h2 := hcmp q 1 hrbr hBRk
  linarith
