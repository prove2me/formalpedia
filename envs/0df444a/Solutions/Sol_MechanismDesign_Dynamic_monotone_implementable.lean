-- Prove2me | solution 1 for MechanismDesign.Dynamic.monotone_implementable
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T10:15:56.635839+00:00
-- url     : https://prove2.me/submissions/1e2e8c21-abee-4634-bfed-44697be5f7db

import Mathlib
import Definitions.Def_MechanismDesign_Dynamic_Model

open MeasureTheory Set

namespace MechanismDesign.Dynamic

def ICg (a b : ℝ) (Q T : ℝ → ℝ) : Prop :=
  ∀ θ ∈ Icc a b, ∀ θ' ∈ Icc a b, θ * Q θ' - T θ' ≤ θ * Q θ - T θ

section Gen
variable {a b : ℝ} {Q T : ℝ → ℝ}

lemma ICg.subgrad (h : ICg a b Q T) {x y : ℝ} (hx : x ∈ Icc a b) (hy : y ∈ Icc a b) :
    (x * Q x - T x) + (y - x) * Q x ≤ y * Q y - T y := by
  have := h y hy x hx; linarith

lemma ICg.mono (h : ICg a b Q T) : MonotoneOn Q (Icc a b) := by
  intro x hx y hy hxy
  rcases eq_or_lt_of_le hxy with rfl | hlt
  · exact le_rfl
  by_contra hc
  push_neg at hc
  have h1 := h.subgrad hx hy
  have h2 := h.subgrad hy hx
  nlinarith [mul_pos (sub_pos.2 hlt) (sub_pos.2 hc)]

lemma ICg.bound (h : ICg a b Q T) {x : ℝ} (hx : x ∈ Icc a b) : |Q x| ≤ |Q a| + |Q b| := by
  have hab : a ≤ b := hx.1.trans hx.2
  have h1 := h.mono ⟨le_rfl, hab⟩ hx hx.1
  have h2 := h.mono hx ⟨hab, le_rfl⟩ hx.2
  rw [abs_le]
  constructor <;> linarith [abs_nonneg (Q a), abs_nonneg (Q b), neg_abs_le (Q a), le_abs_self (Q b)]

lemma ICg.lip (h : ICg a b Q T) {x y : ℝ} (hx : x ∈ Icc a b) (hy : y ∈ Icc a b) :
    |(y * Q y - T y) - (x * Q x - T x)| ≤ (|Q a| + |Q b|) * |y - x| := by
  have h1 := h.subgrad hx hy
  have h2 := h.subgrad hy hx
  have bx := abs_le.1 (h.bound hx)
  have by' := abs_le.1 (h.bound hy)
  rcases le_total x y with hxy | hxy
  · rw [abs_of_nonneg (sub_nonneg.2 hxy), abs_le]
    constructor <;> nlinarith
  · rw [abs_of_nonpos (sub_nonpos.2 hxy), abs_le]
    constructor <;> nlinarith

lemma ICg.lipschitzOnWith (h : ICg a b Q T) :
    LipschitzOnWith (Real.toNNReal (|Q a| + |Q b|)) (fun θ => θ * Q θ - T θ) (Icc a b) := by
  apply LipschitzOnWith.of_dist_le_mul
  intro x hx y hy
  rw [Real.dist_eq, Real.dist_eq, Real.coe_toNNReal _ (by positivity)]
  exact h.lip hy hx

lemma ICg.hasDerivAt (h : ICg a b Q T) {x : ℝ} (hx : x ∈ Ioo a b)
    (hc : ContinuousWithinAt Q (Icc a b) x) :
    HasDerivAt (fun θ => θ * Q θ - T θ) (Q x) x := by
  have hxI : x ∈ Icc a b := Ioo_subset_Icc_self hx
  have hnhds : Icc a b ∈ nhds x := Icc_mem_nhds hx.1 hx.2
  have hca : ContinuousAt Q x := hc.continuousAt hnhds
  rw [hasDerivAt_iff_isLittleO, Asymptotics.isLittleO_iff]
  intro c hc0
  have hev : ∀ᶠ y in nhds x, dist (Q y) (Q x) < c := (Metric.tendsto_nhds.1 hca) c hc0
  filter_upwards [hev, hnhds] with y hy hyI
  have h1 := h.subgrad hxI hyI
  have h2 := h.subgrad hyI hxI
  rw [Real.dist_eq] at hy
  simp only [Real.norm_eq_abs, smul_eq_mul]
  have hq := abs_lt.1 hy
  rcases le_total x y with hxy | hxy
  · rw [abs_of_nonneg (sub_nonneg.2 hxy), abs_le]
    constructor <;> nlinarith
  · rw [abs_of_nonpos (sub_nonpos.2 hxy), abs_le]
    constructor <;> nlinarith

lemma ICg.rep (h : ICg a b Q T) {θ : ℝ} (hθ : θ ∈ Icc a b) :
    θ * Q θ - T θ = (a * Q a - T a) + ∫ x in a..θ, Q x := by
  have hcount := h.mono.countable_not_continuousWithinAt
  have hcont : ContinuousOn (fun θ => θ * Q θ - T θ) (Icc a θ) :=
    h.lipschitzOnWith.continuousOn.mono (Icc_subset_Icc le_rfl hθ.2)
  have hint : IntervalIntegrable Q volume a θ := by
    apply MonotoneOn.intervalIntegrable
    rw [uIcc_of_le hθ.1]
    exact h.mono.mono (Icc_subset_Icc le_rfl hθ.2)
  have := integral_eq_of_hasDerivAt_off_countable_of_le (fun θ => θ * Q θ - T θ) Q hθ.1
    hcount hcont ?_ hint
  · linarith
  · rintro x ⟨hx, hxs⟩
    have hxI : x ∈ Ioo a b := ⟨hx.1, hx.2.trans_le hθ.2⟩
    apply h.hasDerivAt hxI
    by_contra hc
    exact hxs ⟨Ioo_subset_Icc_self hxI, hc⟩

end Gen

lemma swap_tri {a b : ℝ} (hab : a ≤ b) {Q h : ℝ → ℝ} {C : ℝ} (hQ : Measurable Q)
    (hB : ∀ x, |Q x| ≤ C) (hh : IntervalIntegrable h volume a b) :
    ∫ θ in a..b, (∫ x in a..θ, Q x) * h θ = ∫ x in a..b, Q x * ∫ θ in x..b, h θ := by
  set μ := volume.restrict (Ioc a b) with hμ
  have hhi : Integrable h μ := hh.1
  let F : ℝ → ℝ → ℝ := fun θ x => (if x ≤ θ then Q x else 0) * h θ
  have hF : Integrable (Function.uncurry F) (μ.prod μ) := by
    have hg : Integrable (fun p : ℝ × ℝ => h p.1) (μ.prod μ) := hhi.comp_fst μ
    refine hg.bdd_mul (c := C) ?_ ?_
    · exact (Measurable.ite (measurableSet_le measurable_snd measurable_fst)
        (hQ.comp measurable_snd) measurable_const).aestronglyMeasurable
    · refine Filter.Eventually.of_forall fun p => ?_
      simp only [Real.norm_eq_abs]
      split_ifs
      · exact hB _
      · simpa using (abs_nonneg (Q 0)).trans (hB 0)
  have hsw := integral_integral_swap hF
  rw [intervalIntegral.integral_of_le hab, intervalIntegral.integral_of_le hab]
  calc ∫ θ in Ioc a b, (∫ x in a..θ, Q x) * h θ = ∫ θ, ∫ x, F θ x ∂μ ∂μ := by
        apply setIntegral_congr_fun measurableSet_Ioc
        intro θ hθ
        simp only [F]
        rw [integral_mul_const]
        congr 1
        rw [intervalIntegral.integral_of_le hθ.1.le]
        have : (fun x => if x ≤ θ then Q x else 0) = indicator (Iic θ) Q := by
          ext x; simp [indicator]
        rw [this, setIntegral_indicator measurableSet_Iic, Ioc_inter_Iic, min_eq_right hθ.2]
    _ = ∫ x, ∫ θ, F θ x ∂μ ∂μ := hsw
    _ = ∫ x in Ioc a b, Q x * ∫ θ in x..b, h θ := by
        apply setIntegral_congr_fun measurableSet_Ioc
        intro x hx
        simp only [F]
        have : (fun θ => (if x ≤ θ then Q x else 0) * h θ) =
            fun θ => Q x * indicator (Ici x) h θ := by
          ext θ; by_cases hxθ : x ≤ θ <;> simp [indicator, hxθ]
        rw [this, integral_const_mul, setIntegral_indicator measurableSet_Ici,
          intervalIntegral.integral_of_le hx.2]
        congr 1
        have hs : Ioc a b ∩ Ici x = Icc x b := by
          ext y; simp only [mem_inter_iff, mem_Ioc, mem_Ici, mem_Icc]
          constructor
          · rintro ⟨⟨_, h2⟩, h3⟩; exact ⟨h3, h2⟩
          · rintro ⟨h1, h2⟩; exact ⟨⟨hx.1.trans_le h1, h2⟩, h1⟩
        rw [hs, integral_Icc_eq_integral_Ioc]

variable {τlo τhi θlo θhi : ℝ}

lemma exPost_ICg {m : DirectMechanism τlo τhi θlo θhi} (h : m.IsExPostIC) {τ : ℝ}
    (hτ : τ ∈ Icc τlo τhi) : ICg θlo θhi (m.q τ) (m.t τ) :=
  fun θ hθ θ' hθ' => h τ hτ θ hθ θ' hθ'

lemma SeqEnv.tail (E : SeqEnv τlo τhi θlo θhi) {τ : ℝ} (hτ : τ ∈ Icc τlo τhi) {x : ℝ}
    (hx : x ∈ Icc θlo θhi) : ∫ θ in x..θhi, E.f θ τ = 1 - E.F x τ := by
  have h1 : IntervalIntegrable (fun θ => E.f θ τ) volume θlo x :=
    (E.f_integrable τ hτ).mono_set (by
      rw [uIcc_of_le hx.1, uIcc_of_le (hx.1.trans hx.2)]; exact Icc_subset_Icc le_rfl hx.2)
  have h2 : IntervalIntegrable (fun θ => E.f θ τ) volume x θhi :=
    (E.f_integrable τ hτ).mono_set (by
      rw [uIcc_of_le hx.2, uIcc_of_le (hx.1.trans hx.2)]; exact Icc_subset_Icc hx.1 le_rfl)
  rw [E.F_eq τ hτ x hx, ← E.f_total τ hτ,
    ← intervalIntegral.integral_add_adjacent_intervals h1 h2]
  ring

lemma SeqEnv.F_lip (E : SeqEnv τlo τhi θlo θhi) {x : ℝ} (hx : x ∈ Icc θlo θhi) {τ1 τ2 : ℝ}
    (h1 : τ1 ∈ Icc τlo τhi) (h2 : τ2 ∈ Icc τlo τhi) :
    |E.F x τ2 - E.F x τ1| ≤ E.K * |τ2 - τ1| := by
  have := (convex_Icc τlo τhi).norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := fun s => E.F x s) (fun s hs => E.hasDerivWithinAt_F x hx s hs)
    (fun s hs => (E.abs_dFdτ_lt x hx s hs).le) h1 h2
  simpa [Real.norm_eq_abs] using this

lemma SeqEnv.F_anti (E : SeqEnv τlo τhi θlo θhi) {x : ℝ} (hx : x ∈ Icc θlo θhi) {τ1 τ2 : ℝ}
    (h1 : τ1 ∈ Icc τlo τhi) (h2 : τ2 ∈ Icc τlo τhi) (h12 : τ1 ≤ τ2) :
    E.F x τ2 ≤ E.F x τ1 := by
  rcases eq_or_lt_of_le hx.1 with hlo | hlo
  · subst hlo
    rw [E.F_eq τ1 h1 _ hx, E.F_eq τ2 h2 _ hx]; simp
  rcases eq_or_lt_of_le hx.2 with hhi | hhi
  · subst hhi
    rw [E.F_eq τ1 h1 _ hx, E.F_eq τ2 h2 _ hx, E.f_total τ1 h1, E.f_total τ2 h2]
  have hxo : x ∈ Ioo θlo θhi := ⟨hlo, hhi⟩
  have hanti : AntitoneOn (fun s => E.F x s) (Icc τlo τhi) := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc τlo τhi) (f' := fun s => E.dFdτ x s)
    · intro s hs; exact (E.hasDerivWithinAt_F x hx s hs).continuousWithinAt
    · intro s hs
      rw [interior_Icc] at hs ⊢
      exact (E.hasDerivWithinAt_F x hx s (Ioo_subset_Icc_self hs)).mono Ioo_subset_Icc_self
    · intro s hs
      rw [interior_Icc] at hs
      exact (E.fosd x hxo s (Ioo_subset_Icc_self hs)).le
  exact hanti h1 h2 h12

lemma Uhat_diff (E : SeqEnv τlo τhi θlo θhi) (m : DirectMechanism τlo τhi θlo θhi)
    (hm : m.Admissible) (hic : m.IsExPostIC) {τ0 τ1 τ2 : ℝ} (h0 : τ0 ∈ Icc τlo τhi)
    (h1 : τ1 ∈ Icc τlo τhi) (h2 : τ2 ∈ Icc τlo τhi) :
    m.Uhat E τ0 τ2 - m.Uhat E τ0 τ1 =
      ∫ x in θlo..θhi, m.q τ0 x * (E.F x τ1 - E.F x τ2) := by
  have hab : θlo ≤ θhi := E.θlo_lt_θhi.le
  have G := exPost_ICg hic h0
  set Q' : ℝ → ℝ := fun x => m.q τ0 (projIcc θlo θhi hab x) with hQ'
  have hQ'mono : Monotone Q' := fun x y hxy =>
    G.mono (projIcc θlo θhi hab x).2 (projIcc θlo θhi hab y).2 (monotone_projIcc hab hxy)
  have hQ'meas : Measurable Q' := hQ'mono.measurable
  have hQ'B : ∀ x, |Q' x| ≤ 1 := by
    intro x
    have := hm.1 τ0 h0 _ (projIcc θlo θhi hab x).2
    rw [abs_le]; constructor <;> linarith [this.1, this.2]
  have hQ'eq : ∀ x ∈ Icc θlo θhi, Q' x = m.q τ0 x := by
    intro x hx; simp [hQ', projIcc_of_mem hab hx]
  have hcont : ContinuousOn (fun θ => m.u τ0 θ) (uIcc θlo θhi) := by
    rw [uIcc_of_le hab]; exact G.lipschitzOnWith.continuousOn
  have hi : ∀ τ ∈ Icc τlo τhi, IntervalIntegrable (fun θ => m.u τ0 θ * E.f θ τ) volume θlo θhi :=
    fun τ hτ => (E.f_integrable τ hτ).continuousOn_mul hcont
  set W : ℝ → ℝ := fun θ => ∫ x in θlo..θ, Q' x with hW
  have hWc : Continuous W := intervalIntegral.continuous_primitive
    (fun _ _ => hQ'mono.intervalIntegrable) θlo
  set hh : ℝ → ℝ := fun θ => E.f θ τ2 - E.f θ τ1 with hhh
  have hhi : IntervalIntegrable hh volume θlo θhi :=
    (E.f_integrable τ2 h2).sub (E.f_integrable τ1 h1)
  have hu : ∀ θ ∈ uIcc θlo θhi, m.u τ0 θ * E.f θ τ2 - m.u τ0 θ * E.f θ τ1 =
      m.u τ0 θlo * hh θ + W θ * hh θ := by
    intro θ hθ
    rw [uIcc_of_le hab] at hθ
    have hr := G.rep hθ
    have hWθ : W θ = ∫ x in θlo..θ, m.q τ0 x := by
      apply intervalIntegral.integral_congr
      intro x hx
      rw [uIcc_of_le hθ.1] at hx
      exact hQ'eq x ⟨hx.1, hx.2.trans hθ.2⟩
    have hr' : m.u τ0 θ = m.u τ0 θlo + ∫ x in θlo..θ, m.q τ0 x := hr
    rw [hWθ, hr']
    simp only [hhh]
    ring
  unfold DirectMechanism.Uhat
  rw [← intervalIntegral.integral_sub (hi τ2 h2) (hi τ1 h1),
    intervalIntegral.integral_congr hu,
    intervalIntegral.integral_add (hhi.const_mul _) (hhi.continuousOn_mul hWc.continuousOn),
    intervalIntegral.integral_const_mul,
    swap_tri hab hQ'meas hQ'B hhi]
  have h0' : ∫ θ in θlo..θhi, hh θ = 0 := by
    simp only [hhh]
    rw [intervalIntegral.integral_sub (E.f_integrable τ2 h2) (E.f_integrable τ1 h1),
      E.f_total τ2 h2, E.f_total τ1 h1]; ring
  rw [h0', mul_zero, zero_add]
  apply intervalIntegral.integral_congr
  intro x hx
  rw [uIcc_of_le hab] at hx
  simp only [hhh]
  have hx1 : IntervalIntegrable (fun θ => E.f θ τ2) volume x θhi :=
    (E.f_integrable τ2 h2).mono_set (by
      rw [uIcc_of_le hx.2, uIcc_of_le hab]; exact Icc_subset_Icc hx.1 le_rfl)
  have hx2 : IntervalIntegrable (fun θ => E.f θ τ1) volume x θhi :=
    (E.f_integrable τ1 h1).mono_set (by
      rw [uIcc_of_le hx.2, uIcc_of_le hab]; exact Icc_subset_Icc hx.1 le_rfl)
  rw [intervalIntegral.integral_sub hx1 hx2, E.tail h2 hx, E.tail h1 hx, hQ'eq x hx]
  ring

lemma Uhat_le_U (E : SeqEnv τlo τhi θlo θhi) (m : DirectMechanism τlo τhi θlo θhi)
    (hic : m.IsIC E) {τ τ' : ℝ} (hτ : τ ∈ Icc τlo τhi) (hτ' : τ' ∈ Icc τlo τhi) :
    m.Uhat E τ' τ ≤ m.U E τ :=
  hic.2 τ hτ τ' hτ' id measurable_id (fun _ hθ => hθ)

lemma U_mono_core (E : SeqEnv τlo τhi θlo θhi) (m : DirectMechanism τlo τhi θlo θhi)
    (hm : m.Admissible) (hic : m.IsIC E) : MonotoneOn (m.U E) (Icc τlo τhi) := by
  intro τ1 h1 τ2 h2 h12
  have hd := Uhat_diff E m hm hic.1 h1 h1 h2
  have hnn : 0 ≤ ∫ x in θlo..θhi, m.q τ1 x * (E.F x τ1 - E.F x τ2) := by
    apply intervalIntegral.integral_nonneg E.θlo_lt_θhi.le
    intro x hx
    exact mul_nonneg (hm.1 τ1 h1 x hx).1 (sub_nonneg.2 (E.F_anti hx h1 h2 h12))
  have := Uhat_le_U E m hic h2 h1
  unfold DirectMechanism.U at *
  linarith

lemma U_lip_core (E : SeqEnv τlo τhi θlo θhi) (m : DirectMechanism τlo τhi θlo θhi)
    (hm : m.Admissible) (hic : m.IsIC E) {τ1 τ2 : ℝ} (h1 : τ1 ∈ Icc τlo τhi)
    (h2 : τ2 ∈ Icc τlo τhi) :
    |m.U E τ2 - m.U E τ1| ≤ E.K * (θhi - θlo) * |τ2 - τ1| := by
  have hab : θlo ≤ θhi := E.θlo_lt_θhi.le
  have key : ∀ s1 s2, s1 ∈ Icc τlo τhi → s2 ∈ Icc τlo τhi → s1 ≤ s2 →
      |m.U E s2 - m.U E s1| ≤ E.K * (θhi - θlo) * |s2 - s1| := by
    intro s1 s2 g1 g2 g12
    have hmono := U_mono_core E m hm hic g1 g2 g12
    have hd := Uhat_diff E m hm hic.1 g2 g1 g2
    have hle := Uhat_le_U E m hic g1 g2
    have hb : ‖∫ x in θlo..θhi, m.q s2 x * (E.F x s1 - E.F x s2)‖ ≤
        (E.K * |s2 - s1|) * |θhi - θlo| := by
      apply intervalIntegral.norm_integral_le_of_norm_le_const
      intro x hx
      have hx' : x ∈ Icc θlo θhi := by
        rw [uIoc_of_le hab] at hx; exact Ioc_subset_Icc_self hx
      have hq := hm.1 s2 g2 x hx'
      have hF := E.F_lip hx' g1 g2
      rw [Real.norm_eq_abs, abs_mul, abs_sub_comm]
      calc |m.q s2 x| * |E.F x s2 - E.F x s1| ≤ 1 * (E.K * |s2 - s1|) := by
            apply mul_le_mul _ hF (abs_nonneg _) zero_le_one
            rw [abs_le]; constructor <;> linarith [hq.1, hq.2]
        _ = _ := one_mul _
    rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.2 hab)] at hb
    have hb' := (le_abs_self _).trans hb
    unfold DirectMechanism.U at *
    rw [abs_of_nonneg (sub_nonneg.2 hmono)]
    nlinarith
  rcases le_total τ1 τ2 with h | h
  · exact key τ1 τ2 h1 h2 h
  · rw [abs_sub_comm, abs_sub_comm τ2]; exact key τ2 τ1 h2 h1 h

theorem Umac_core {τlo τhi θlo θhi : ℝ} (E : SeqEnv τlo τhi θlo θhi)
    (m : DirectMechanism τlo τhi θlo θhi) (hm : m.Admissible) (hic : m.IsIC E) :
    MonotoneOn (m.U E) (Set.Icc τlo τhi) ∧ AbsolutelyContinuousOnInterval (m.U E) τlo τhi := by
  refine ⟨U_mono_core E m hm hic, ?_⟩
  apply LipschitzOnWith.absolutelyContinuousOnInterval (K := Real.toNNReal (E.K * (θhi - θlo)))
  rw [uIcc_of_le E.τlo_lt_τhi.le]
  apply LipschitzOnWith.of_dist_le_mul
  intro x hx y hy
  rw [Real.dist_eq, Real.dist_eq, Real.coe_toNNReal _ (mul_nonneg E.K_pos.le
    (sub_nonneg.2 E.θlo_lt_θhi.le))]
  exact U_lip_core E m hm hic hy hx

theorem irr_core {τlo τhi θlo θhi : ℝ} (E : SeqEnv τlo τhi θlo θhi)
    (m : DirectMechanism τlo τhi θlo θhi) (hm : m.Admissible) (hic : m.IsIC E) :
    m.IsIR E ↔ 0 ≤ m.U E τlo := by
  constructor
  · intro h; exact h τlo ⟨le_rfl, E.τlo_lt_τhi.le⟩
  · intro h τ hτ
    exact h.trans (U_mono_core E m hm hic ⟨le_rfl, E.τlo_lt_τhi.le⟩ hτ hτ.1)


theorem icc_core {τlo τhi θlo θhi : ℝ} (E : SeqEnv τlo τhi θlo θhi)
    (m : DirectMechanism τlo τhi θlo θhi) (hm : m.Admissible) :
    m.IsIC E ↔ m.IsExPostIC ∧
      ∀ τ ∈ Set.Icc τlo τhi, ∀ τ' ∈ Set.Icc τlo τhi, m.Uhat E τ' τ ≤ m.U E τ := by
  constructor
  · intro hic
    exact ⟨hic.1, fun τ hτ τ' hτ' => Uhat_le_U E m hic hτ hτ'⟩
  rintro ⟨hpost, hU⟩
  refine ⟨hpost, fun τ hτ τ' hτ' θr hθr hθrI => ?_⟩
  have hab : θlo ≤ θhi := E.θlo_lt_θhi.le
  have G := exPost_ICg hpost hτ'
  have hcont : ContinuousOn (fun θ => m.u τ' θ) (uIcc θlo θhi) := by
    rw [uIcc_of_le hab]; exact G.lipschitzOnWith.continuousOn
  have hR : IntervalIntegrable (fun θ => m.u τ' θ * E.f θ τ) volume θlo θhi :=
    (E.f_integrable τ hτ).continuousOn_mul hcont
  -- measurability of the misreport integrand
  have hqs : Measurable (fun y : Icc θlo θhi => m.q τ' y) :=
    hm.2.1.comp ((measurable_const (a := (⟨τ', hτ'⟩ : Icc τlo τhi))).prodMk measurable_id)
  have hts : Measurable (fun y : Icc θlo θhi => m.t τ' y) :=
    hm.2.2.comp ((measurable_const (a := (⟨τ', hτ'⟩ : Icc τlo τhi))).prodMk measurable_id)
  have hproj : Measurable (fun θ => projIcc θlo θhi hab (θr θ)) :=
    continuous_projIcc.measurable.comp hθr
  set ψ : ℝ → ℝ := fun θ => θ * m.q τ' (projIcc θlo θhi hab (θr θ)) -
    m.t τ' (projIcc θlo θhi hab (θr θ)) with hψ
  have hψm : Measurable ψ :=
    (measurable_id.mul (hqs.comp hproj)).sub (hts.comp hproj)
  have hψeq : ∀ θ ∈ Icc θlo θhi, ψ θ = θ * m.q τ' (θr θ) - m.t τ' (θr θ) := by
    intro θ hθ
    simp only [hψ, projIcc_of_mem hab (hθrI θ hθ)]
  set Lc := |m.q τ' θlo| + |m.q τ' θhi| with hLc
  have htb : ∀ y ∈ Icc θlo θhi, |m.t τ' y| ≤ θhi + |m.u τ' θlo| + Lc * (θhi - θlo) := by
    intro y hy
    have h1 := G.lip ⟨le_rfl, hab⟩ hy
    have hq := hm.1 τ' hτ' y hy
    have hy0 : 0 ≤ y := E.θlo_nonneg.trans hy.1
    have hyq : 0 ≤ y * m.q τ' y := mul_nonneg hy0 hq.1
    have hyq' : y * m.q τ' y ≤ θhi := by nlinarith [hq.2, hy.2]
    rw [abs_of_nonneg (sub_nonneg.2 hy.1)] at h1
    have hu : |m.u τ' y| ≤ |m.u τ' θlo| + Lc * (y - θlo) := by
      have := abs_sub_abs_le_abs_sub (m.u τ' y) (m.u τ' θlo)
      have h1' : |m.u τ' y - m.u τ' θlo| ≤ Lc * (y - θlo) := h1
      linarith
    have hLc0 : 0 ≤ Lc := by positivity
    have : Lc * (y - θlo) ≤ Lc * (θhi - θlo) := mul_le_mul_of_nonneg_left (by linarith [hy.2]) hLc0
    have ht : m.t τ' y = y * m.q τ' y - m.u τ' y := by simp [DirectMechanism.u]
    rw [ht]
    have := abs_le.1 hu
    rw [abs_le]; constructor <;> linarith
  have hL : IntervalIntegrable
      (fun θ => (θ * m.q τ' (θr θ) - m.t τ' (θr θ)) * E.f θ τ) volume θlo θhi := by
    have hfi := (E.f_integrable τ hτ).1
    refine ⟨?_, by rw [Ioc_eq_empty (not_lt.2 hab)]; exact integrableOn_empty⟩
    refine hfi.bdd_mul (c := θhi + (θhi + |m.u τ' θlo| + Lc * (θhi - θlo))) ?_ ?_
    · refine hψm.aestronglyMeasurable.congr ?_
      refine (ae_restrict_iff' measurableSet_Ioc).2 (Filter.Eventually.of_forall fun θ hθ => ?_)
      exact hψeq θ (Ioc_subset_Icc_self hθ)
    · refine (ae_restrict_iff' measurableSet_Ioc).2 (Filter.Eventually.of_forall fun θ hθ => ?_)
      have hθ' := Ioc_subset_Icc_self hθ
      have hy := hθrI θ hθ'
      have hq := hm.1 τ' hτ' _ hy
      have hθ0 : 0 ≤ θ := E.θlo_nonneg.trans hθ'.1
      have h1 : 0 ≤ θ * m.q τ' (θr θ) := mul_nonneg hθ0 hq.1
      have h2 : θ * m.q τ' (θr θ) ≤ θhi := by nlinarith [hq.2, hθ'.2]
      have h3 := abs_le.1 (htb _ hy)
      rw [Real.norm_eq_abs, abs_le]; constructor <;> linarith
  calc ∫ θ in θlo..θhi, (θ * m.q τ' (θr θ) - m.t τ' (θr θ)) * E.f θ τ
      ≤ ∫ θ in θlo..θhi, m.u τ' θ * E.f θ τ := by
        apply intervalIntegral.integral_mono_on hab hL hR
        intro θ hθ
        exact mul_le_mul_of_nonneg_right (hpost τ' hτ' θ hθ (θr θ) (hθrI θ hθ))
          (E.f_pos θ hθ τ hτ).le
    _ = m.Uhat E τ' τ := rfl
    _ ≤ m.U E τ := hU τ hτ τ' hτ'


lemma ii_of_bound {g : ℝ → ℝ} {a b C : ℝ} (hab : a ≤ b) (hg : Measurable g)
    (hB : ∀ s ∈ Icc a b, |g s| ≤ C) : IntervalIntegrable g volume a b := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab]
  refine Measure.integrableOn_of_bounded (M := C) (by simp) hg.aestronglyMeasurable ?_
  refine (ae_restrict_iff' measurableSet_Ioc).2 (Filter.Eventually.of_forall fun s hs => ?_)
  simpa [Real.norm_eq_abs] using hB s (Ioc_subset_Icc_self hs)

lemma SeqEnv.dF_nonpos (E : SeqEnv τlo τhi θlo θhi) {x : ℝ} (hx : x ∈ Icc θlo θhi) {s : ℝ}
    (hs : s ∈ Icc τlo τhi) : E.dFdτ x s ≤ 0 := by
  rcases eq_or_lt_of_le hx.1 with h | h
  · have hc : HasDerivWithinAt (fun s => E.F x s) 0 (Icc τlo τhi) s := by
      refine (hasDerivWithinAt_const s _ (0:ℝ)).congr (fun y hy => ?_) ?_
      · rw [E.F_eq y hy _ hx, ← h]; simp
      · rw [E.F_eq s hs _ hx, ← h]; simp
    have := (uniqueDiffOn_Icc E.τlo_lt_τhi s hs).eq_deriv _ (E.hasDerivWithinAt_F _ hx s hs) hc
    linarith
  rcases eq_or_lt_of_le hx.2 with h' | h'
  · have hc : HasDerivWithinAt (fun s => E.F x s) 0 (Icc τlo τhi) s := by
      refine (hasDerivWithinAt_const s _ (1:ℝ)).congr (fun y hy => ?_) ?_
      · rw [E.F_eq y hy _ hx, h', E.f_total y hy]
      · rw [E.F_eq s hs _ hx, h', E.f_total s hs]
    have := (uniqueDiffOn_Icc E.τlo_lt_τhi s hs).eq_deriv _ (E.hasDerivWithinAt_F _ hx s hs) hc
    linarith
  · exact (E.fosd x ⟨h, h'⟩ s hs).le

lemma fub_L (E : SeqEnv τlo τhi θlo θhi) {Q : ℝ → ℝ} (hQ : Measurable Q) (hQB : ∀ x, |Q x| ≤ 1)
    {a b : ℝ} (hab : a ≤ b) (ha : a ∈ Icc τlo τhi) (hb : b ∈ Icc τlo τhi) :
    ∫ x in θlo..θhi, Q x * (E.F x b - E.F x a) =
      ∫ s in a..b, ∫ x in θlo..θhi, Q x * E.dFdτ x s := by
  have hθ : θlo ≤ θhi := E.θlo_lt_θhi.le
  have hsub : Icc a b ⊆ Icc τlo τhi := Icc_subset_Icc ha.1 hb.2
  have hftc : ∀ x ∈ Icc θlo θhi, E.F x b - E.F x a = ∫ s in a..b, E.dFdτ x s := by
    intro x hx
    symm
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab
    · exact fun s hs => ((E.hasDerivWithinAt_F x hx s (hsub hs)).continuousWithinAt).mono hsub
    · intro s hs
      have hs' : s ∈ Ioo τlo τhi := ⟨ha.1.trans_lt hs.1, hs.2.trans_le hb.2⟩
      exact (E.hasDerivWithinAt_F x hx s (Ioo_subset_Icc_self hs')).hasDerivAt
        (Icc_mem_nhds hs'.1 hs'.2)
    · exact ((E.continuousOn_dFdτ x hx).mono hsub).intervalIntegrable_of_Icc hab
  set μ := volume.restrict (Ioc θlo θhi) with hμ
  set ν := volume.restrict (Ioc a b) with hν
  have hmeas : Measurable (fun p : ℝ × ℝ => Q p.1 * E.dFdτ p.1 p.2) :=
    (hQ.comp measurable_fst).mul (E.dFdτ_measurable.comp measurable_swap)
  have hint : Integrable (fun p : ℝ × ℝ => Q p.1 * E.dFdτ p.1 p.2) (μ.prod ν) := by
    refine (integrable_const E.K).mono' hmeas.aestronglyMeasurable ?_
    rw [hμ, hν, Measure.prod_restrict]
    refine (ae_restrict_iff' (measurableSet_Ioc.prod measurableSet_Ioc)).2
      (Filter.Eventually.of_forall fun p hp => ?_)
    have hx := Ioc_subset_Icc_self hp.1
    have hs := hsub (Ioc_subset_Icc_self hp.2)
    rw [Real.norm_eq_abs, abs_mul]
    calc |Q p.1| * |E.dFdτ p.1 p.2| ≤ 1 * E.K :=
          mul_le_mul (hQB _) (E.abs_dFdτ_lt _ hx _ hs).le (abs_nonneg _) zero_le_one
      _ = E.K := one_mul _
  have hsw := integral_integral_swap (f := fun x s => Q x * E.dFdτ x s) hint
  rw [intervalIntegral.integral_of_le hθ, intervalIntegral.integral_of_le hab]
  calc ∫ x in Ioc θlo θhi, Q x * (E.F x b - E.F x a)
      = ∫ x, ∫ s, Q x * E.dFdτ x s ∂ν ∂μ := by
        apply setIntegral_congr_fun measurableSet_Ioc
        intro x hx
        simp only
        rw [hftc x (Ioc_subset_Icc_self hx), intervalIntegral.integral_of_le hab,
          integral_const_mul]
    _ = ∫ s, ∫ x, Q x * E.dFdτ x s ∂μ ∂ν := hsw
    _ = _ := by
        apply setIntegral_congr_fun measurableSet_Ioc
        intro s _
        simp only
        rw [intervalIntegral.integral_of_le hθ]

theorem mi_core {τlo τhi θlo θhi : ℝ} (E : SeqEnv τlo τhi θlo θhi)
    (q : ℝ → ℝ → ℝ)
    (hq : ∀ τ ∈ Set.Icc τlo τhi, ∀ θ ∈ Set.Icc θlo θhi, q τ θ ∈ Set.Icc (0 : ℝ) 1)
    (hqm : Measurable (fun p : Set.Icc τlo τhi × Set.Icc θlo θhi => q p.1 p.2))
    (hτ : ∀ θ ∈ Set.Icc θlo θhi, MonotoneOn (fun τ => q τ θ) (Set.Icc τlo τhi))
    (hθ : ∀ τ ∈ Set.Icc τlo τhi, MonotoneOn (q τ) (Set.Icc θlo θhi)) :
    ∃ t : ℝ → ℝ → ℝ, (⟨q, t⟩ : DirectMechanism τlo τhi θlo θhi).Admissible ∧
      (⟨q, t⟩ : DirectMechanism τlo τhi θlo θhi).IsIC E := by
  have hT : τlo ≤ τhi := E.τlo_lt_τhi.le
  have hΘ : θlo ≤ θhi := E.θlo_lt_θhi.le
  set qt : ℝ → ℝ → ℝ := fun τ x => q (projIcc τlo τhi hT τ) (projIcc θlo θhi hΘ x) with hqt
  have hqtm : Measurable (fun p : ℝ × ℝ => qt p.1 p.2) :=
    hqm.comp (((continuous_projIcc : Continuous (projIcc τlo τhi hT)).measurable.comp
      measurable_fst).prodMk
      ((continuous_projIcc : Continuous (projIcc θlo θhi hΘ)).measurable.comp measurable_snd))
  have hqt_eq : ∀ τ ∈ Icc τlo τhi, ∀ x ∈ Icc θlo θhi, qt τ x = q τ x := by
    intro τ hτ' x hx; simp [hqt, projIcc_of_mem hT hτ', projIcc_of_mem hΘ hx]
  have hqt01 : ∀ τ x, qt τ x ∈ Icc (0:ℝ) 1 := fun τ x =>
    hq _ (projIcc τlo τhi hT τ).2 _ (projIcc θlo θhi hΘ x).2
  have hqtB : ∀ τ x, |qt τ x| ≤ 1 := fun τ x => by
    rw [abs_le]; constructor <;> linarith [(hqt01 τ x).1, (hqt01 τ x).2]
  have hqt_mx : ∀ τ, Monotone (qt τ) := fun τ x y hxy =>
    hθ _ (projIcc τlo τhi hT τ).2 (projIcc θlo θhi hΘ x).2 (projIcc θlo θhi hΘ y).2
      (monotone_projIcc hΘ hxy)
  have hqt_mτ : ∀ x, Monotone (fun τ => qt τ x) := fun x τ1 τ2 h =>
    hτ _ (projIcc θlo θhi hΘ x).2 (projIcc τlo τhi hT τ1).2 (projIcc τlo τhi hT τ2).2
      (monotone_projIcc hT h)
  have hqtmx : ∀ τ, Measurable (qt τ) := fun τ => (hqt_mx τ).measurable
  set μθ := volume.restrict (Ioc θlo θhi) with hμθ
  -- W
  set W : ℝ → ℝ → ℝ := fun τ θ => ∫ x, (if x ≤ θ then qt τ x else 0) ∂μθ with hWdef
  have hWm : Measurable (fun p : ℝ × ℝ => W p.1 p.2) := by
    have : StronglyMeasurable (fun p : (ℝ × ℝ) × ℝ => if p.2 ≤ p.1.2 then qt p.1.1 p.2 else 0) :=
      (Measurable.ite (measurableSet_le measurable_snd (measurable_snd.comp measurable_fst))
        (hqtm.comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd))
        measurable_const).stronglyMeasurable
    exact (this.integral_prod_right' (ν := μθ)).measurable
  have hWeq : ∀ τ θ, θ ∈ Icc θlo θhi → W τ θ = ∫ x in θlo..θ, qt τ x := by
    intro τ θ hθ'
    simp only [hWdef]
    rw [intervalIntegral.integral_of_le hθ'.1]
    have : (fun x => if x ≤ θ then qt τ x else 0) = indicator (Iic θ) (qt τ) := by
      ext x; simp [indicator]
    rw [this, setIntegral_indicator measurableSet_Iic, Ioc_inter_Iic, min_eq_right hθ'.2]
  have hWc : ∀ τ, ContinuousOn (W τ) (Icc θlo θhi) := by
    intro τ
    exact (intervalIntegral.continuous_primitive (fun _ _ => (hqt_mx τ).intervalIntegrable)
      θlo).continuousOn.congr (fun θ hθ' => hWeq τ θ hθ')
  -- D, Φ
  set D : ℝ → ℝ := fun s => ∫ x in θlo..θhi, qt s x * E.dFdτ x (projIcc τlo τhi hT s) with hD
  have hDm : Measurable D := by
    have hmap : Measurable (fun p : ℝ × ℝ => (((projIcc τlo τhi hT p.1 : Icc τlo τhi) : ℝ), p.2)) :=
      (measurable_subtype_coe.comp ((continuous_projIcc : Continuous (projIcc τlo τhi hT)).measurable.comp
          measurable_fst)).prodMk measurable_snd
    have h0 : Measurable (fun p : ℝ × ℝ =>
        qt p.1 p.2 * E.dFdτ p.2 (projIcc τlo τhi hT p.1)) :=
      hqtm.mul (E.dFdτ_measurable.comp hmap)
    have h1 := h0.stronglyMeasurable
    have h2 := (h1.integral_prod_right' (ν := μθ)).measurable
    have : D = fun s => ∫ x, qt s x * E.dFdτ x (projIcc τlo τhi hT s) ∂μθ := by
      ext s; simp only [hD, hμθ, intervalIntegral.integral_of_le hΘ]
    rw [this]; exact h2
  have hDB : ∀ s, |D s| ≤ E.K * (θhi - θlo) := by
    intro s
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := θlo) (b := θhi)
      (C := E.K) (f := fun x => qt s x * E.dFdτ x (projIcc τlo τhi hT s)) (by
        intro x hx
        rw [uIoc_of_le hΘ] at hx
        have hx' := Ioc_subset_Icc_self hx
        rw [Real.norm_eq_abs, abs_mul]
        calc |qt s x| * |E.dFdτ x (projIcc τlo τhi hT s)| ≤ 1 * E.K :=
              mul_le_mul (hqtB _ _) (E.abs_dFdτ_lt _ hx' _ (projIcc τlo τhi hT s).2).le
                (abs_nonneg _) zero_le_one
          _ = E.K := one_mul _)
    rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.2 hΘ)] at this
    exact this
  have hDii : ∀ a b, IntervalIntegrable D volume a b := by
    intro a b
    rcases le_total a b with h | h
    · exact ii_of_bound h hDm (fun s _ => hDB s)
    · exact (ii_of_bound h hDm (fun s _ => hDB s)).symm
  have hDeq : ∀ s ∈ Icc τlo τhi, D s = ∫ x in θlo..θhi, qt s x * E.dFdτ x s := by
    intro s hs; simp only [hD, projIcc_of_mem hT hs]
  set Φ : ℝ → ℝ := fun τ => -∫ s in τlo..τ, D s with hΦ
  have hΦm : Measurable Φ :=
    (intervalIntegral.continuous_primitive hDii τlo).measurable.neg
  -- c and t
  set c : ℝ → ℝ := fun τ => Φ τ - ∫ θ in θlo..θhi, W τ θ * E.f θ τ with hc
  have hcm : Measurable c := by
    have h1 : StronglyMeasurable (fun p : ℝ × ℝ => W p.1 p.2 * E.f p.2 p.1) :=
      (hWm.mul E.f_measurable).stronglyMeasurable
    have h2 := (h1.integral_prod_right' (ν := μθ)).measurable
    have : (fun τ => ∫ θ in θlo..θhi, W τ θ * E.f θ τ) = fun τ => ∫ θ, W τ θ * E.f θ τ ∂μθ := by
      ext τ; simp only [hμθ, intervalIntegral.integral_of_le hΘ]
    exact hΦm.sub (this ▸ h2)
  set t : ℝ → ℝ → ℝ := fun τ θ => θ * q τ θ - W τ θ - c τ with ht
  set m : DirectMechanism τlo τhi θlo θhi := ⟨q, t⟩ with hmdef
  have hadm : m.Admissible := by
    refine ⟨hq, hqm, ?_⟩
    show Measurable (fun p : Icc τlo τhi × Icc θlo θhi =>
      (p.2 : ℝ) * q p.1 p.2 - W p.1 p.2 - c p.1)
    exact (((measurable_subtype_coe.comp measurable_snd).mul hqm).sub
      (hWm.comp ((measurable_subtype_coe.comp measurable_fst).prodMk
        (measurable_subtype_coe.comp measurable_snd)))).sub
      (hcm.comp (measurable_subtype_coe.comp measurable_fst))
  have hpost : m.IsExPostIC := by
    intro τ hτ' θ hθ' θ' hθ''
    show θ * q τ θ' - (θ' * q τ θ' - W τ θ' - c τ) ≤ θ * q τ θ - (θ * q τ θ - W τ θ - c τ)
    rw [hWeq τ θ hθ', hWeq τ θ' hθ'', ← hqt_eq τ hτ' θ' hθ'']
    have key := intervalIntegral.integral_interval_sub_left (a := θlo) (b := θ) (c := θ')
      ((hqt_mx τ).intervalIntegrable (μ := volume)) ((hqt_mx τ).intervalIntegrable (μ := volume))
    rcases le_total θ' θ with h | h
    · have := intervalIntegral.integral_mono_on h (intervalIntegrable_const (μ := volume) (c := qt τ θ'))
        ((hqt_mx τ).intervalIntegrable) (fun x hx => hqt_mx τ hx.1)
      rw [intervalIntegral.integral_const, smul_eq_mul] at this
      linarith
    · have := intervalIntegral.integral_mono_on h ((hqt_mx τ).intervalIntegrable)
        (intervalIntegrable_const (μ := volume) (c := qt τ θ')) (fun x hx => hqt_mx τ hx.2)
      rw [intervalIntegral.integral_const, smul_eq_mul] at this
      have hs : ∫ x in θ'..θ, qt τ x = -∫ x in θ..θ', qt τ x := intervalIntegral.integral_symm _ _
      linarith
  refine ⟨t, hadm, (icc_core E m hadm).2 ⟨hpost, ?_⟩⟩
  -- U = Φ
  have hUΦ : ∀ r ∈ Icc τlo τhi, m.U E r = Φ r := by
    intro r hr
    have hWi : IntervalIntegrable (fun θ => W r θ * E.f θ r) volume θlo θhi :=
      (E.f_integrable r hr).continuousOn_mul (by rw [uIcc_of_le hΘ]; exact hWc r)
    have : m.U E r = ∫ θ in θlo..θhi, (W r θ * E.f θ r + c r * E.f θ r) := by
      unfold DirectMechanism.U DirectMechanism.Uhat
      apply intervalIntegral.integral_congr
      intro θ _
      simp only [DirectMechanism.u, hmdef, ht]
      ring
    rw [this, intervalIntegral.integral_add hWi ((E.f_integrable r hr).const_mul _),
      intervalIntegral.integral_const_mul, E.f_total r hr]
    simp only [hc]; ring
  intro τ hτ' τ' hτ''
  have hdiff := Uhat_diff E m hadm hpost hτ'' hτ'' hτ'
  rw [hUΦ τ hτ', show m.Uhat E τ' τ' = m.U E τ' from rfl, hUΦ τ' hτ''] at *
  have hconv : ∫ x in θlo..θhi, m.q τ' x * (E.F x τ' - E.F x τ) =
      ∫ x in θlo..θhi, qt τ' x * (E.F x τ' - E.F x τ) := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [uIcc_of_le hΘ] at hx
    simp only [hmdef]
    rw [hqt_eq τ' hτ'' x hx]
  rw [hconv] at hdiff
  -- A
  have hAi : ∀ a b, a ≤ b → Icc a b ⊆ Icc τlo τhi →
      IntervalIntegrable (fun s => ∫ x in θlo..θhi, qt τ' x * E.dFdτ x s) volume a b := by
    intro a b hab hsub
    have hm1 : Measurable (fun s => ∫ x in θlo..θhi, qt τ' x * E.dFdτ x s) := by
      have h1 : StronglyMeasurable (fun p : ℝ × ℝ => qt τ' p.2 * E.dFdτ p.2 p.1) :=
        ((hqtmx τ').comp measurable_snd |>.mul E.dFdτ_measurable).stronglyMeasurable
      have h2 := (h1.integral_prod_right' (ν := μθ)).measurable
      have : (fun s => ∫ x in θlo..θhi, qt τ' x * E.dFdτ x s) =
          fun s => ∫ x, qt τ' x * E.dFdτ x s ∂μθ := by
        ext s; simp only [hμθ, intervalIntegral.integral_of_le hΘ]
      rw [this]; exact h2
    refine ii_of_bound hab hm1 (C := E.K * (θhi - θlo)) (fun s hs => ?_)
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := θlo) (b := θhi)
      (C := E.K) (f := fun x => qt τ' x * E.dFdτ x s) (by
        intro x hx
        rw [uIoc_of_le hΘ] at hx
        have hx' := Ioc_subset_Icc_self hx
        rw [Real.norm_eq_abs, abs_mul]
        calc |qt τ' x| * |E.dFdτ x s| ≤ 1 * E.K :=
              mul_le_mul (hqtB _ _) (E.abs_dFdτ_lt _ hx' _ (hsub hs)).le
                (abs_nonneg _) zero_le_one
          _ = E.K := one_mul _)
    rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.2 hΘ)] at this
    exact this
  have hxint : ∀ r s, s ∈ Icc τlo τhi →
      IntervalIntegrable (fun x => qt r x * E.dFdτ x s) volume θlo θhi := by
    intro r s hs
    refine ii_of_bound hΘ ((hqtmx r).mul (E.dFdτ_measurable.comp
      (measurable_const.prodMk measurable_id))) (C := E.K) (fun x hx => ?_)
    rw [abs_mul]
    calc |qt r x| * |E.dFdτ x s| ≤ 1 * E.K :=
          mul_le_mul (hqtB _ _) (E.abs_dFdτ_lt _ hx _ hs).le (abs_nonneg _) zero_le_one
      _ = E.K := one_mul _
  rcases le_total τ τ' with h | h
  · have hsub : Icc τ τ' ⊆ Icc τlo τhi := Icc_subset_Icc hτ'.1 hτ''.2
    have hL := fub_L E (hqtmx τ') (hqtB τ') h hτ' hτ''
    have hΦd : Φ τ - Φ τ' = ∫ s in τ..τ', D s := by
      simp only [hΦ]
      rw [← intervalIntegral.integral_interval_sub_left (hDii τlo τ') (hDii τlo τ)]
      ring
    have hle : ∫ s in τ..τ', (∫ x in θlo..θhi, qt τ' x * E.dFdτ x s) ≤ ∫ s in τ..τ', D s := by
      apply intervalIntegral.integral_mono_on h (hAi τ τ' h hsub) (hDii τ τ')
      intro s hs
      rw [hDeq s (hsub hs)]
      apply intervalIntegral.integral_mono_on hΘ (hxint τ' s (hsub hs)) (hxint s s (hsub hs))
      intro x hx
      exact mul_le_mul_of_nonpos_right (hqt_mτ x hs.2) (E.dF_nonpos hx (hsub hs))
    linarith
  · have hsub : Icc τ' τ ⊆ Icc τlo τhi := Icc_subset_Icc hτ''.1 hτ'.2
    have hL := fub_L E (hqtmx τ') (hqtB τ') h hτ'' hτ'
    have hneg : ∫ x in θlo..θhi, qt τ' x * (E.F x τ' - E.F x τ) =
        -∫ x in θlo..θhi, qt τ' x * (E.F x τ - E.F x τ') := by
      rw [← intervalIntegral.integral_neg]
      congr 1; ext x; ring
    have hΦd : Φ τ - Φ τ' = -∫ s in τ'..τ, D s := by
      simp only [hΦ]
      rw [← intervalIntegral.integral_interval_sub_left (hDii τlo τ) (hDii τlo τ')]
      ring
    have hle : ∫ s in τ'..τ, D s ≤ ∫ s in τ'..τ, (∫ x in θlo..θhi, qt τ' x * E.dFdτ x s) := by
      apply intervalIntegral.integral_mono_on h (hDii τ' τ) (hAi τ' τ h hsub)
      intro s hs
      rw [hDeq s (hsub hs)]
      apply intervalIntegral.integral_mono_on hΘ (hxint s s (hsub hs)) (hxint τ' s (hsub hs))
      intro x hx
      exact mul_le_mul_of_nonpos_right (hqt_mτ x hs.1) (E.dF_nonpos hx (hsub hs))
    linarith

end MechanismDesign.Dynamic

open MechanismDesign.Dynamic


theorem solution {τlo τhi θlo θhi : ℝ} (E : SeqEnv τlo τhi θlo θhi)
    (q : ℝ → ℝ → ℝ)
    (hq : ∀ τ ∈ Set.Icc τlo τhi, ∀ θ ∈ Set.Icc θlo θhi, q τ θ ∈ Set.Icc (0 : ℝ) 1)
    (hqm : Measurable (fun p : Set.Icc τlo τhi × Set.Icc θlo θhi => q p.1 p.2))
    (hτ : ∀ θ ∈ Set.Icc θlo θhi, MonotoneOn (fun τ => q τ θ) (Set.Icc τlo τhi))
    (hθ : ∀ τ ∈ Set.Icc τlo τhi, MonotoneOn (q τ) (Set.Icc θlo θhi)) :
    ∃ t : ℝ → ℝ → ℝ, (⟨q, t⟩ : DirectMechanism τlo τhi θlo θhi).Admissible ∧
      (⟨q, t⟩ : DirectMechanism τlo τhi θlo θhi).IsIC E := by
  exact mi_core E q hq hqm hτ hθ
