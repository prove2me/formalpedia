-- Prove2me | solution 1 for InfoBargaining.Uniform.gain_shape
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T05:45:45.565411+00:00
-- url     : https://prove2.me/submissions/022e8040-2549-497b-8f35-9b1d9efdcfdc

import Mathlib
import Definitions.Def_InfoBargaining_Uniform_Setting

set_option autoImplicit false
open InfoBargaining.Uniform

lemma ib_int_lin (α d a b : ℝ) :
    ∫ w in a..b, (α * w + d) = α * (b ^ 2 - a ^ 2) / 2 + d * (b - a) := by
  have h1 : IntervalIntegrable (fun w : ℝ => α * w) MeasureTheory.volume a b :=
    (by fun_prop : Continuous fun w : ℝ => α * w).intervalIntegrable _ _
  have h2 : IntervalIntegrable (fun _ : ℝ => d) MeasureTheory.volume a b :=
    (by fun_prop : Continuous fun _ : ℝ => d).intervalIntegrable _ _
  rw [intervalIntegral.integral_add h1 h2]
  rw [intervalIntegral.integral_const_mul, integral_id, intervalIntegral.integral_const]
  simp
  ring

lemma ib_cont (α c : ℝ) : Continuous fun w : ℝ => max (α * w + (1 - α) / 2 - c) 0 := by
  fun_prop

lemma ib_A_eq (α c : ℝ) (hα : 0 < α) :
    A α c = max (1 / 2 - c) 0 + (max (α - |1 - 2 * c|) 0) ^ 2 / (8 * α) := by
  unfold A
  rcases le_or_gt α (1 - 2 * c) with h1 | h1
  · -- integrand nonneg
    have : ∫ w in (0:ℝ)..1, max (α * w + (1 - α) / 2 - c) 0
        = ∫ w in (0:ℝ)..1, (α * w + ((1 - α) / 2 - c)) := by
      apply intervalIntegral.integral_congr
      intro w hw
      rw [Set.uIcc_of_le zero_le_one] at hw
      simp only
      rw [max_eq_left (by nlinarith [hw.1, hw.2])]
      ring
    rw [this, ib_int_lin]
    have hs : |1 - 2 * c| = 1 - 2 * c := abs_of_nonneg (by linarith)
    rw [hs, max_eq_left (by linarith : 1 / 2 - c ≥ 0), max_eq_right (by linarith : α - (1 - 2 * c) ≤ 0)]
    ring
  rcases le_or_gt (1 - 2 * c) (-α) with h2 | h2
  · have : ∫ w in (0:ℝ)..1, max (α * w + (1 - α) / 2 - c) 0 = ∫ w in (0:ℝ)..1, (0:ℝ) := by
      apply intervalIntegral.integral_congr
      intro w hw
      rw [Set.uIcc_of_le zero_le_one] at hw
      simp only
      rw [max_eq_right (by nlinarith [hw.1, hw.2])]
    rw [this]
    have hs : |1 - 2 * c| = -(1 - 2 * c) := abs_of_nonpos (by linarith)
    rw [hs, max_eq_right (by linarith : 1 / 2 - c ≤ 0), max_eq_right (by linarith : α - -(1 - 2 * c) ≤ 0)]
    simp
  · -- middle case
    set w0 : ℝ := (α - (1 - 2 * c)) / (2 * α) with hw0
    have hw0a : 0 < w0 := by rw [hw0]; apply div_pos <;> linarith
    have hw0b : w0 < 1 := by rw [hw0, div_lt_one (by linarith)]; linarith
    have hαw0 : α * w0 = (α - (1 - 2 * c)) / 2 := by rw [hw0]; field_simp
    have hsplit := intervalIntegral.integral_add_adjacent_intervals
      ((ib_cont α c).intervalIntegrable (μ := MeasureTheory.volume) 0 w0)
      ((ib_cont α c).intervalIntegrable (μ := MeasureTheory.volume) w0 1)
    rw [← hsplit]
    have e1 : ∫ w in (0:ℝ)..w0, max (α * w + (1 - α) / 2 - c) 0 = ∫ w in (0:ℝ)..w0, (0:ℝ) := by
      apply intervalIntegral.integral_congr
      intro w hw
      rw [Set.uIcc_of_le hw0a.le] at hw
      simp only
      rw [max_eq_right]
      have : α * w ≤ α * w0 := mul_le_mul_of_nonneg_left hw.2 hα.le
      linarith
    have e2 : ∫ w in w0..1, max (α * w + (1 - α) / 2 - c) 0
        = ∫ w in w0..1, (α * w + ((1 - α) / 2 - c)) := by
      apply intervalIntegral.integral_congr
      intro w hw
      rw [Set.uIcc_of_le hw0b.le] at hw
      simp only
      rw [max_eq_left]
      · ring
      · have : α * w0 ≤ α * w := mul_le_mul_of_nonneg_left hw.1 hα.le
        linarith
    rw [e1, e2, ib_int_lin]
    simp only [intervalIntegral.integral_const, smul_zero, zero_add]
    have key : α * (1 ^ 2 - w0 ^ 2) / 2 + ((1 - α) / 2 - c) * (1 - w0)
        = (α + (1 - 2 * c)) ^ 2 / (8 * α) := by
      rw [hw0]; field_simp; ring
    rw [key]
    rcases le_total 0 (1 - 2 * c) with h3 | h3
    · rw [abs_of_nonneg h3, max_eq_left (by linarith : 1 / 2 - c ≥ 0),
        max_eq_left (by linarith : α - (1 - 2 * c) ≥ 0)]
      field_simp; ring
    · rw [abs_of_nonpos h3, max_eq_right (by linarith : 1 / 2 - c ≤ 0),
        max_eq_left (by linarith : α - -(1 - 2 * c) ≥ 0)]
      field_simp; ring


lemma ib_A_convex (c : ℝ) : ConvexOn ℝ (Set.Ioo (0:ℝ) 1) (fun α => A α c) := by
  refine ⟨convex_Ioo 0 1, ?_⟩
  intro x _ y _ a b ha hb hab
  simp only [smul_eq_mul]
  unfold A
  have hix := (ib_cont x c).intervalIntegrable (μ := MeasureTheory.volume) 0 1
  have hiy := (ib_cont y c).intervalIntegrable (μ := MeasureTheory.volume) 0 1
  rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul,
    ← intervalIntegral.integral_add (hix.const_mul a) (hiy.const_mul b)]
  apply intervalIntegral.integral_mono_on zero_le_one
  · exact (ib_cont (a * x + b * y) c).intervalIntegrable _ _
  · exact (hix.const_mul a).add (hiy.const_mul b)
  · intro w _
    have e : (a * x + b * y) * w + (1 - (a * x + b * y)) / 2 - c
        = a * (x * w + (1 - x) / 2 - c) + b * (y * w + (1 - y) / 2 - c) := by
      have : b = 1 - a := by linarith
      subst this; ring
    rw [e]
    apply max_le
    · have h1 := le_max_left (x * w + (1 - x) / 2 - c) 0
      have h2 := le_max_left (y * w + (1 - y) / 2 - c) 0
      nlinarith
    · have h1 := le_max_right (x * w + (1 - x) / 2 - c) 0
      have h2 := le_max_right (y * w + (1 - y) / 2 - c) 0
      nlinarith

noncomputable def ibGam (a b t : ℝ) : ℝ :=
  (max (b - t) 0) ^ 2 / (8 * b) - (max (a - t) 0) ^ 2 / (8 * a)

lemma ib_gain_eq (M : Model) (c : ℝ) : M.gain c = ibGam M.αlo M.αhi |1 - 2 * c| := by
  have hb : 0 < M.αhi := lt_trans M.αlo_pos M.αlo_lt_αhi
  unfold Model.gain ibGam
  rw [ib_A_eq _ _ hb, ib_A_eq _ _ M.αlo_pos]; ring

lemma ib_Gam_lo (a b t : ℝ) (ha : 0 < a) (hab : a < b) (ht0 : 0 ≤ t) (hta : t ≤ a) :
    ibGam a b t = (b - a) * (a * b - t ^ 2) / (8 * a * b) := by
  have hb : 0 < b := lt_trans ha hab
  unfold ibGam
  rw [max_eq_left (by linarith : b - t ≥ 0), max_eq_left (by linarith : a - t ≥ 0)]
  field_simp
  ring

lemma ib_Gam_hi (a b t : ℝ) (ha : 0 < a) (hab : a < b) (hat : a ≤ t) :
    ibGam a b t = (max (b - t) 0) ^ 2 / (8 * b) := by
  unfold ibGam
  rw [max_eq_right (by linarith : a - t ≤ 0)]
  simp

lemma ib_Gam_ge (a b t : ℝ) (ha : 0 < a) (hab : a < b) (hbt : b ≤ t) : ibGam a b t = 0 := by
  rw [ib_Gam_hi a b t ha hab (by linarith), max_eq_right (by linarith : b - t ≤ 0)]
  simp

lemma ib_Gam_L1 (a b t1 t2 : ℝ) (ha : 0 < a) (hab : a < b) (h0 : 0 ≤ t1) (h12 : t1 < t2)
    (h2a : t2 ≤ a) : ibGam a b t2 < ibGam a b t1 := by
  have hb : 0 < b := lt_trans ha hab
  rw [ib_Gam_lo a b t1 ha hab h0 (by linarith), ib_Gam_lo a b t2 ha hab (by linarith) h2a]
  have h8 : 0 < 8 * a * b := by positivity
  rw [div_lt_div_iff_of_pos_right h8]
  have : t1 ^ 2 < t2 ^ 2 := by nlinarith
  have hba : 0 < b - a := by linarith
  nlinarith

lemma ib_Gam_L2 (a b t1 t2 : ℝ) (ha : 0 < a) (hab : a < b) (h0 : a ≤ t1) (h12 : t1 < t2)
    (h2b : t2 ≤ b) : ibGam a b t2 < ibGam a b t1 := by
  have hb : 0 < b := lt_trans ha hab
  rw [ib_Gam_hi a b t1 ha hab h0, ib_Gam_hi a b t2 ha hab (by linarith)]
  rw [max_eq_left (by linarith : b - t1 ≥ 0), max_eq_left (by linarith : b - t2 ≥ 0)]
  apply div_lt_div_of_pos_right _ (by positivity)
  nlinarith

lemma ib_Gam_anti (a b t1 t2 : ℝ) (ha : 0 < a) (hab : a < b) (h0 : 0 ≤ t1) (h12 : t1 < t2)
    (h2b : t2 ≤ b) : ibGam a b t2 < ibGam a b t1 := by
  by_cases h2a : t2 ≤ a
  · exact ib_Gam_L1 a b t1 t2 ha hab h0 h12 h2a
  · by_cases h1a : a ≤ t1
    · exact ib_Gam_L2 a b t1 t2 ha hab h1a h12 h2b
    · push_neg at h2a h1a
      exact lt_trans (ib_Gam_L2 a b a t2 ha hab le_rfl h2a h2b)
        (ib_Gam_L1 a b t1 a ha hab h0 h1a le_rfl)

lemma ib_Gam_b (a b : ℝ) (ha : 0 < a) (hab : a < b) : ibGam a b b = 0 :=
  ib_Gam_ge a b b ha hab le_rfl

lemma ib_Gam_nonneg (a b t : ℝ) (ha : 0 < a) (hab : a < b) (h0 : 0 ≤ t) : 0 ≤ ibGam a b t := by
  rcases lt_or_ge t b with h | h
  · have := ib_Gam_anti a b t b ha hab h0 h le_rfl
    rw [ib_Gam_b a b ha hab] at this
    exact this.le
  · rw [ib_Gam_ge a b t ha hab h]

lemma ib_Gam_pos (a b t : ℝ) (ha : 0 < a) (hab : a < b) (h0 : 0 ≤ t) (htb : t < b) :
    0 < ibGam a b t := by
  have := ib_Gam_anti a b t b ha hab h0 htb le_rfl
  rwa [ib_Gam_b a b ha hab] at this

lemma ib_Gam_zero (a b : ℝ) (ha : 0 < a) (hab : a < b) : ibGam a b 0 = (b - a) / 8 := by
  have hb : 0 < b := lt_trans ha hab
  rw [ib_Gam_lo a b 0 ha hab le_rfl ha.le]
  field_simp
  ring

lemma ib_Gam_cont (a b : ℝ) : Continuous (ibGam a b) := by
  unfold ibGam
  fun_prop

lemma ib_Gam_le (a b t : ℝ) (ha : 0 < a) (hab : a < b) (h0 : 0 ≤ t) :
    ibGam a b t ≤ (b - a) / 8 := by
  rw [← ib_Gam_zero a b ha hab]
  rcases eq_or_lt_of_le h0 with h | h
  · rw [← h]
  · rcases le_or_gt t b with h2 | h2
    · exact (ib_Gam_anti a b 0 t ha hab le_rfl h h2).le
    · rw [ib_Gam_ge a b t ha hab h2.le]
      exact ib_Gam_nonneg a b 0 ha hab le_rfl

/-! Buyer objective -/

lemma ib_k_lo (M : Model) : M.k M.αlo = 0 := by
  unfold Model.k; simp

lemma ib_k_hi (M : Model) : M.k M.αhi = M.kbar := by
  unfold Model.k
  have : M.αhi - M.αlo ≠ 0 := by linarith [M.αlo_lt_αhi]
  field_simp

lemma ib_Ub_diff (M : Model) (θb c : ℝ) :
    M.Ub θb c M.αhi - M.Ub θb c M.αlo = θb * M.gain c - M.kbar := by
  unfold Model.Ub Model.gain
  rw [ib_k_lo, ib_k_hi]; ring

lemma ib_Ub_convex (M : Model) (θb c : ℝ) (hθ : 0 ≤ θb) :
    ∀ x ∈ Set.Icc M.αlo M.αhi, ∀ y ∈ Set.Icc M.αlo M.αhi, ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → a + b = 1 →
      M.Ub θb c (a * x + b * y) ≤ a * M.Ub θb c x + b * M.Ub θb c y := by
  intro x hx y hy a b ha hb hab
  have hlo := M.αlo_pos
  have hhi := M.αhi_lt_one
  have hxI : x ∈ Set.Ioo (0:ℝ) 1 := ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hyI : y ∈ Set.Ioo (0:ℝ) 1 := ⟨by linarith [hy.1], by linarith [hy.2]⟩
  have h := (ib_A_convex c).2 hxI hyI ha hb hab
  simp only [smul_eq_mul] at h
  have hk : M.k (a * x + b * y) = a * M.k x + b * M.k y := by
    unfold Model.k
    have : b = 1 - a := by linarith
    subst this
    field_simp
    ring
  unfold Model.Ub
  rw [hk]
  nlinarith

lemma ib_corner (M : Model) (θb c : ℝ) (hθ : 0 ≤ θb) :
    ∀ α ∈ Set.Icc M.αlo M.αhi,
      M.Ub θb c α ≤ max (M.Ub θb c M.αlo) (M.Ub θb c M.αhi) ∧
      (M.Ub θb c M.αlo ≠ M.Ub θb c M.αhi → α ≠ M.αlo → α ≠ M.αhi →
        M.Ub θb c α < max (M.Ub θb c M.αlo) (M.Ub θb c M.αhi)) := by
  intro α hα
  have hd : 0 < M.αhi - M.αlo := by linarith [M.αlo_lt_αhi]
  set b : ℝ := (α - M.αlo) / (M.αhi - M.αlo) with hb
  set a : ℝ := (M.αhi - α) / (M.αhi - M.αlo) with ha
  have ha0 : 0 ≤ a := div_nonneg (by linarith [hα.2]) hd.le
  have hb0 : 0 ≤ b := div_nonneg (by linarith [hα.1]) hd.le
  have hab : a + b = 1 := by rw [ha, hb]; field_simp; ring
  have hα' : a * M.αlo + b * M.αhi = α := by rw [ha, hb]; field_simp; ring
  have hmain := ib_Ub_convex M θb c hθ M.αlo ⟨le_rfl, M.αlo_lt_αhi.le⟩ M.αhi
    ⟨M.αlo_lt_αhi.le, le_rfl⟩ a b ha0 hb0 hab
  rw [hα'] at hmain
  set U1 := M.Ub θb c M.αlo
  set U2 := M.Ub θb c M.αhi
  constructor
  · refine hmain.trans ?_
    rcases le_total U1 U2 with h | h
    · rw [max_eq_right h]
      have : a * U1 + b * U2 = U2 - a * (U2 - U1) := by linear_combination U2 * hab
      nlinarith [mul_nonneg ha0 (sub_nonneg.2 h)]
    · rw [max_eq_left h]
      have : a * U1 + b * U2 = U1 - b * (U1 - U2) := by linear_combination U1 * hab
      nlinarith [mul_nonneg hb0 (sub_nonneg.2 h)]
  · intro hne hlo hhi
    have ha1 : 0 < a := by
      rcases ha0.lt_or_eq with h | h
      · exact h
      · exfalso; apply hhi
        have : b = 1 := by linarith
        rw [← hα', ← h, this]; ring
    have hb1 : 0 < b := by
      rcases hb0.lt_or_eq with h | h
      · exact h
      · exfalso; apply hlo
        have : a = 1 := by linarith
        rw [← hα', ← h, this]; ring
    refine lt_of_le_of_lt hmain ?_
    rcases lt_or_gt_of_ne hne with h | h
    · rw [max_eq_right h.le]
      have : a * U1 + b * U2 = U2 - a * (U2 - U1) := by linear_combination U2 * hab
      nlinarith [mul_pos ha1 (sub_pos.2 h)]
    · rw [max_eq_left h.le]
      have : a * U1 + b * U2 = U1 - b * (U1 - U2) := by linear_combination U1 * hab
      nlinarith [mul_pos hb1 (sub_pos.2 h)]

lemma ib_opt_cases (M : Model) (θb c : ℝ) (hθ : 0 ≤ θb) :
    (M.Ub θb c M.αlo < M.Ub θb c M.αhi → M.optSet θb c = {M.αhi}) ∧
    (M.Ub θb c M.αhi < M.Ub θb c M.αlo → M.optSet θb c = {M.αlo}) ∧
    (M.Ub θb c M.αlo = M.Ub θb c M.αhi → M.αlo ∈ M.optSet θb c ∧ M.αhi ∈ M.optSet θb c) := by
  have hlh := M.αlo_lt_αhi
  have hloI : M.αlo ∈ Set.Icc M.αlo M.αhi := ⟨le_rfl, hlh.le⟩
  have hhiI : M.αhi ∈ Set.Icc M.αlo M.αhi := ⟨hlh.le, le_rfl⟩
  refine ⟨?_, ?_, ?_⟩
  · intro h
    ext α
    simp only [Set.mem_singleton_iff]
    constructor
    · rintro ⟨hα, hopt⟩
      by_contra hne
      have hlo : α ≠ M.αlo := by
        rintro rfl; have := hopt _ hhiI; linarith
      have := (ib_corner M θb c hθ α hα).2 h.ne hlo hne
      have h2 := hopt _ hhiI
      rw [max_eq_right h.le] at this
      linarith
    · rintro rfl
      refine ⟨hhiI, fun α' hα' => ?_⟩
      have := (ib_corner M θb c hθ α' hα').1
      rwa [max_eq_right h.le] at this
  · intro h
    ext α
    simp only [Set.mem_singleton_iff]
    constructor
    · rintro ⟨hα, hopt⟩
      by_contra hne
      have hhi : α ≠ M.αhi := by
        rintro rfl; have := hopt _ hloI; linarith
      have := (ib_corner M θb c hθ α hα).2 h.ne' hne hhi
      have h2 := hopt _ hloI
      rw [max_eq_left h.le] at this
      linarith
    · rintro rfl
      refine ⟨hloI, fun α' hα' => ?_⟩
      have := (ib_corner M θb c hθ α' hα').1
      rwa [max_eq_left h.le] at this
  · intro h
    constructor
    · refine ⟨hloI, fun α' hα' => ?_⟩
      have := (ib_corner M θb c hθ α' hα').1
      rwa [← h, max_self] at this
    · refine ⟨hhiI, fun α' hα' => ?_⟩
      have := (ib_corner M θb c hθ α' hα').1
      rwa [← h, max_self, h] at this


lemma ib_Gam_lt_zero (a b t : ℝ) (ha : 0 < a) (hab : a < b) (h0 : 0 < t) :
    ibGam a b t < (b - a) / 8 := by
  rw [← ib_Gam_zero a b ha hab]
  rcases le_or_gt t b with h2 | h2
  · exact ib_Gam_anti a b 0 t ha hab le_rfl h0 h2
  · rw [ib_Gam_ge a b t ha hab h2.le]
    rw [ib_Gam_zero a b ha hab]; linarith

lemma ib_A_first (α c : ℝ) (hα : 0 < α) (h : α ≤ |1 - 2 * c|) : A α c = max (1 / 2 - c) 0 := by
  rw [ib_A_eq α c hα, max_eq_right (by linarith : α - |1 - 2 * c| ≤ 0)]
  simp

lemma ib_A_second (α c : ℝ) (hα : 0 < α) (h : |1 - 2 * c| ≤ α) :
    A α c = ((1 + α) / 2 - c) ^ 2 / (2 * α) := by
  rw [ib_A_eq α c hα, max_eq_left (by linarith : α - |1 - 2 * c| ≥ 0)]
  rcases le_total 0 (1 - 2 * c) with h3 | h3
  · rw [abs_of_nonneg h3, max_eq_left (by linarith : 1 / 2 - c ≥ 0)]
    field_simp; ring
  · rw [abs_of_nonpos h3, max_eq_right (by linarith : 1 / 2 - c ≤ 0)]
    field_simp; ring

lemma ib_lo_mem (M : Model) (θb c : ℝ) (hθ : 0 ≤ θb) (h : θb * M.gain c ≤ M.kbar) :
    M.αlo ∈ M.optSet θb c := by
  have hd := ib_Ub_diff M θb c
  obtain ⟨h1, h2, h3⟩ := ib_opt_cases M θb c hθ
  rcases lt_trichotomy (M.Ub θb c M.αlo) (M.Ub θb c M.αhi) with h | h | h
  · exfalso; linarith
  · exact (h3 h).1
  · rw [h2 h]; rfl

lemma ib_lo_only (M : Model) (θb c : ℝ) (hθ : 0 ≤ θb) (h : θb * M.gain c < M.kbar) :
    M.optSet θb c = {M.αlo} := by
  have hd := ib_Ub_diff M θb c
  exact (ib_opt_cases M θb c hθ).2.1 (by linarith)

lemma ib_hi_only (M : Model) (θb c : ℝ) (hθ : 0 ≤ θb) (h : M.kbar < θb * M.gain c) :
    M.optSet θb c = {M.αhi} := by
  have hd := ib_Ub_diff M θb c
  exact (ib_opt_cases M θb c hθ).1 (by linarith)


theorem solution (M : Model) :
    (∀ c ∈ Set.Ioo (0:ℝ) 1, (c ≤ (1 - M.αhi) / 2 ∨ (1 + M.αhi) / 2 ≤ c) → M.gain c = 0) ∧
    (∀ c ∈ Set.Ioo (0:ℝ) 1, 0 ≤ M.gain c) ∧
    (∀ c ∈ Set.Ioo ((1 - M.αhi) / 2) ((1 + M.αhi) / 2), 0 < M.gain c) ∧
    StrictMonoOn M.gain (Set.Icc ((1 - M.αhi) / 2) (1 / 2)) ∧
    StrictAntiOn M.gain (Set.Icc (1 / 2) ((1 + M.αhi) / 2)) ∧
    M.gain (1 / 2) = (M.αhi - M.αlo) / 8 := by
  have ha := M.αlo_pos
  have hab := M.αlo_lt_αhi
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro c _ h
    rw [ib_gain_eq]
    apply ib_Gam_ge _ _ _ ha hab
    rcases h with h | h
    · exact le_abs.2 (Or.inl (by linarith))
    · exact le_abs.2 (Or.inr (by linarith))
  · intro c _
    rw [ib_gain_eq]
    exact ib_Gam_nonneg _ _ _ ha hab (abs_nonneg _)
  · intro c hc
    rw [ib_gain_eq]
    apply ib_Gam_pos _ _ _ ha hab (abs_nonneg _)
    rw [abs_lt]
    constructor <;> linarith [hc.1, hc.2]
  · intro x hx y hy hxy
    rw [ib_gain_eq, ib_gain_eq]
    rw [abs_of_nonneg (by linarith [hx.2] : 0 ≤ 1 - 2 * x), abs_of_nonneg (by linarith [hy.2] : 0 ≤ 1 - 2 * y)]
    exact ib_Gam_anti _ _ (1 - 2 * y) (1 - 2 * x) ha hab (by linarith [hy.2]) (by linarith)
      (by linarith [hx.1])
  · intro x hx y hy hxy
    rw [ib_gain_eq, ib_gain_eq]
    rw [abs_of_nonpos (by linarith [hx.1] : 1 - 2 * x ≤ 0), abs_of_nonpos (by linarith [hy.1] : 1 - 2 * y ≤ 0)]
    have := ib_Gam_anti M.αlo M.αhi (-(1 - 2 * x)) (-(1 - 2 * y)) ha hab (by linarith [hx.1])
      (by linarith) (by linarith [hy.2])
    exact this
  · rw [ib_gain_eq]
    have : |1 - 2 * (1 / 2 : ℝ)| = 0 := by norm_num
    rw [this, ib_Gam_zero _ _ ha hab]
