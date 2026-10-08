-- Prove2me | solution 1 for MechanismDesign.Dynamic.transfer_formula
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T10:10:06.16835+00:00
-- url     : https://prove2.me/submissions/835a136f-52c4-4cf0-a007-43e839fdfd17

import Mathlib
import Definitions.Def_MechanismDesign_Dynamic_Model
import Definitions.Def_MechanismDesign_Dynamic_OptimalScreening

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


lemma qmeas_ext (E : SeqEnv τlo τhi θlo θhi) (m : DirectMechanism τlo τhi θlo θhi)
    (hic : m.IsExPostIC) {τ : ℝ} (hτ : τ ∈ Icc τlo τhi) :
    AEStronglyMeasurable (fun x => m.q τ x) (volume.restrict (Ioc θlo θhi)) := by
  have hab : θlo ≤ θhi := E.θlo_lt_θhi.le
  have G := exPost_ICg hic hτ
  have hmono : Monotone (fun x => m.q τ (projIcc θlo θhi hab x)) := fun x y hxy =>
    G.mono (projIcc θlo θhi hab x).2 (projIcc θlo θhi hab y).2 (monotone_projIcc hab hxy)
  refine hmono.measurable.aestronglyMeasurable.congr ?_
  refine (ae_restrict_iff' measurableSet_Ioc).2 (Filter.Eventually.of_forall fun x hx => ?_)
  simp [projIcc_of_mem hab (Ioc_subset_Icc_self hx)]

lemma env_deriv (E : SeqEnv τlo τhi θlo θhi) (m : DirectMechanism τlo τhi θlo θhi)
    (hm : m.Admissible) (hic : m.IsIC E) {τ : ℝ} (hτ : τ ∈ Ioo τlo τhi) :
    HasDerivAt (fun s => m.Uhat E τ s) (-∫ θ in θlo..θhi, m.q τ θ * E.dFdτ θ τ) τ := by
  have hab : θlo ≤ θhi := E.θlo_lt_θhi.le
  have hτI : τ ∈ Icc τlo τhi := Ioo_subset_Icc_self hτ
  set μ := volume.restrict (Ioc θlo θhi) with hμ
  let Fn : ℝ → ℝ → ℝ := fun s x => m.q τ x * (E.F x τ - E.F x s)
  let F' : ℝ → ℝ → ℝ := fun s x => m.q τ x * -(E.dFdτ x s)
  have hqm := qmeas_ext E m hic.1 hτI
  have hFc : ∀ s ∈ Icc τlo τhi, AEStronglyMeasurable (fun x => E.F x s) μ := by
    intro s hs
    have hc : ContinuousOn (fun x => E.F x s) (Icc θlo θhi) := by
      have := intervalIntegral.continuousOn_primitive_interval
        ((intervalIntegrable_iff').1 (E.f_integrable s hs))
      rw [uIcc_of_le hab] at this
      exact this.congr (fun x hx => E.F_eq s hs x hx)
    exact (hc.aestronglyMeasurable measurableSet_Icc).mono_measure
      (Measure.restrict_mono Ioc_subset_Icc_self le_rfl)
  have hnhds : Ioo τlo τhi ∈ nhds τ := Ioo_mem_nhds hτ.1 hτ.2
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ) (F := Fn) (F' := F')
    (bound := fun _ => E.K) hnhds
    (Filter.eventually_of_mem hnhds fun s hs =>
      hqm.mul ((hFc τ hτI).sub (hFc s (Ioo_subset_Icc_self hs))))
    (by
      have : Fn τ = fun _ => 0 := by ext x; simp [Fn]
      rw [this]; exact integrable_zero _ _ _)
    (hqm.mul ((E.dFdτ_measurable.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable.neg))
    (by
      refine (ae_restrict_iff' measurableSet_Ioc).2 (Filter.Eventually.of_forall fun x hx s hs => ?_)
      have hx' := Ioc_subset_Icc_self hx
      have hq := hm.1 τ hτI x hx'
      have hK := E.abs_dFdτ_lt x hx' s (Ioo_subset_Icc_self hs)
      simp only [F', Real.norm_eq_abs, abs_mul, abs_neg]
      calc |m.q τ x| * |E.dFdτ x s| ≤ 1 * E.K := by
            apply mul_le_mul _ hK.le (abs_nonneg _) zero_le_one
            rw [abs_le]; constructor <;> linarith [hq.1, hq.2]
        _ = E.K := one_mul _)
    (integrable_const _)
    (by
      refine (ae_restrict_iff' measurableSet_Ioc).2 (Filter.Eventually.of_forall fun x hx s hs => ?_)
      have hx' := Ioc_subset_Icc_self hx
      have hd : HasDerivAt (fun s => E.F x s) (E.dFdτ x s) s :=
        (E.hasDerivWithinAt_F x hx' s (Ioo_subset_Icc_self hs)).hasDerivAt
          (Icc_mem_nhds hs.1 hs.2)
      exact (hd.const_sub (E.F x τ)).const_mul (m.q τ x))
  have hφ := key.2
  -- identify
  have hev : (fun s => m.Uhat E τ s) =ᶠ[nhds τ] fun s => m.Uhat E τ τ + ∫ x, Fn s x ∂μ := by
    filter_upwards [hnhds] with s hs
    have := Uhat_diff E m hm hic.1 hτI hτI (Ioo_subset_Icc_self hs)
    rw [intervalIntegral.integral_of_le hab] at this
    simp only [Fn]
    linarith
  have hval : ∫ x, F' τ x ∂μ = -∫ θ in θlo..θhi, m.q τ θ * E.dFdτ θ τ := by
    rw [intervalIntegral.integral_of_le hab, ← integral_neg]
    simp only [F', mul_neg, hμ]
  rw [← hval]
  exact (hφ.const_add _).congr_of_eventuallyEq hev

lemma env_derivU (E : SeqEnv τlo τhi θlo θhi) (m : DirectMechanism τlo τhi θlo θhi)
    (hm : m.Admissible) (hic : m.IsIC E) {τ : ℝ} (hτ : τ ∈ Ioo τlo τhi)
    (hd : DifferentiableAt ℝ (m.U E) τ) :
    HasDerivAt (m.U E) (-∫ θ in θlo..θhi, m.q τ θ * E.dFdτ θ τ) τ := by
  have h1 := env_deriv E m hm hic hτ
  have hmin : IsLocalMin (fun s => m.U E s - m.Uhat E τ s) τ := by
    filter_upwards [Ioo_mem_nhds hτ.1 hτ.2] with s hs
    have := Uhat_le_U E m hic (Ioo_subset_Icc_self hs) (Ioo_subset_Icc_self hτ)
    simp only [DirectMechanism.U] at this ⊢
    linarith
  have h0 := hmin.hasDerivAt_eq_zero (hd.hasDerivAt.sub h1)
  have : deriv (m.U E) τ = -∫ θ in θlo..θhi, m.q τ θ * E.dFdτ θ τ := by linarith
  rw [← this]; exact hd.hasDerivAt

lemma env_int (E : SeqEnv τlo τhi θlo θhi) (m : DirectMechanism τlo τhi θlo θhi)
    (hm : m.Admissible) (hic : m.IsIC E) {τ : ℝ} (hτ : τ ∈ Icc τlo τhi) :
    m.U E τ - m.U E τlo = ∫ s in τlo..τ, -∫ θ in θlo..θhi, m.q s θ * E.dFdτ θ s := by
  have hac := (Umac_core E m hm hic).2.mono (c := τlo) (d := τ) (by
    rw [uIcc_of_le hτ.1, uIcc_of_le E.τlo_lt_τhi.le]; exact Icc_subset_Icc le_rfl hτ.2)
  rw [← hac.integral_deriv_eq_sub]
  apply intervalIntegral.integral_congr_ae
  have hmono : MonotoneOn (m.U E) (Ioo τlo τhi) :=
    (Umac_core E m hm hic).1.mono Ioo_subset_Icc_self
  filter_upwards [hmono.ae_differentiableWithinAt_of_mem,
    measure_eq_zero_iff_ae_notMem.1 (measure_singleton τhi)] with s hs hne hsI
  rw [uIoc_of_le hτ.1] at hsI
  have hsO : s ∈ Ioo τlo τhi := ⟨hsI.1, lt_of_le_of_ne (hsI.2.trans hτ.2) (by simpa using hne)⟩
  have hd := (hs hsO).differentiableAt (Ioo_mem_nhds hsO.1 hsO.2)
  exact (env_derivU E m hm hic hsO hd).deriv

theorem tf_core {τlo τhi θlo θhi : ℝ} (E : SeqEnv τlo τhi θlo θhi)
    (m : DirectMechanism τlo τhi θlo θhi) (hm : m.Admissible) (hic : m.IsIC E) :
    ∀ τ ∈ Set.Icc τlo τhi, ∀ θ ∈ Set.Icc θlo θhi,
      m.t τ θ = E.t0 m.q (m.t τlo θlo) τ + θ * m.q τ θ - ∫ x in θlo..θ, m.q τ x := by
  intro τ hτ θ hθ
  have hab : θlo ≤ θhi := E.θlo_lt_θhi.le
  have hlo : τlo ∈ Icc τlo τhi := ⟨le_rfl, E.τlo_lt_τhi.le⟩
  have hI := env_int E m hm hic hτ
  rw [intervalIntegral.integral_neg] at hI
  have hqi : ∀ r ∈ Icc τlo τhi, ∀ y ∈ Icc θlo θhi,
      IntervalIntegrable (fun x => m.q r x) volume θlo y := by
    intro r hr y hy
    apply MonotoneOn.intervalIntegrable
    rw [uIcc_of_le hy.1]
    exact (exPost_ICg hic.1 hr).mono.mono (Icc_subset_Icc le_rfl hy.2)
  have hW : ∀ r ∈ Icc τlo τhi,
      ∫ y in θlo..θhi, (∫ x in θlo..y, m.q r x) * E.f y r = m.U E r - m.u r θlo := by
    intro r hr
    have G := exPost_ICg hic.1 hr
    have hcont : ContinuousOn (fun θ => m.u r θ) (uIcc θlo θhi) := by
      rw [uIcc_of_le hab]; exact G.lipschitzOnWith.continuousOn
    have hi : IntervalIntegrable (fun θ => m.u r θ * E.f θ r) volume θlo θhi :=
      (E.f_integrable r hr).continuousOn_mul hcont
    have : ∫ y in θlo..θhi, (∫ x in θlo..y, m.q r x) * E.f y r =
        ∫ y in θlo..θhi, (m.u r y * E.f y r - m.u r θlo * E.f y r) := by
      apply intervalIntegral.integral_congr
      intro y hy
      rw [uIcc_of_le hab] at hy
      have hr' : m.u r y = m.u r θlo + ∫ x in θlo..y, m.q r x := G.rep hy
      simp only
      rw [hr']; ring
    rw [this, intervalIntegral.integral_sub hi ((E.f_integrable r hr).const_mul _),
      intervalIntegral.integral_const_mul, E.f_total r hr]
    simp [DirectMechanism.U, DirectMechanism.Uhat]
  have hJ : ∫ θ' in θlo..θhi, ∫ x in θlo..θ', (m.q τ x * E.f θ' τ - m.q τlo x * E.f θ' τlo) =
      (m.U E τ - m.u τ θlo) - (m.U E τlo - m.u τlo θlo) := by
    rw [← hW τ hτ, ← hW τlo hlo]
    have e : ∫ θ' in θlo..θhi, ∫ x in θlo..θ', (m.q τ x * E.f θ' τ - m.q τlo x * E.f θ' τlo) =
        ∫ θ' in θlo..θhi, ((∫ x in θlo..θ', m.q τ x) * E.f θ' τ -
          (∫ x in θlo..θ', m.q τlo x) * E.f θ' τlo) := by
      apply intervalIntegral.integral_congr
      intro y hy
      rw [uIcc_of_le hab] at hy
      simp only
      rw [intervalIntegral.integral_sub ((hqi τ hτ y hy).mul_const _)
        ((hqi τlo hlo y hy).mul_const _), intervalIntegral.integral_mul_const,
        intervalIntegral.integral_mul_const]
    have hWi : ∀ r ∈ Icc τlo τhi, IntervalIntegrable
        (fun y => (∫ x in θlo..y, m.q r x) * E.f y r) volume θlo θhi := by
      intro r hr
      have hc : ContinuousOn (fun y => ∫ x in θlo..y, m.q r x) (uIcc θlo θhi) :=
        intervalIntegral.continuousOn_primitive_interval
          ((intervalIntegrable_iff').1 (hqi r hr θhi ⟨hab, le_rfl⟩))
      exact (E.f_integrable r hr).continuousOn_mul hc
    rw [e, intervalIntegral.integral_sub (hWi τ hτ) (hWi τlo hlo)]
  have hrep : m.u τ θ = m.u τ θlo + ∫ x in θlo..θ, m.q τ x := (exPost_ICg hic.1 hτ).rep hθ
  unfold SeqEnv.t0
  rw [hJ]
  simp only [DirectMechanism.u] at hrep hJ ⊢
  linarith

end MechanismDesign.Dynamic

open MechanismDesign.Dynamic


theorem solution {τlo τhi θlo θhi : ℝ} (E : SeqEnv τlo τhi θlo θhi)
    (m : DirectMechanism τlo τhi θlo θhi) (hm : m.Admissible) (hic : m.IsIC E) :
    ∀ τ ∈ Set.Icc τlo τhi, ∀ θ ∈ Set.Icc θlo θhi,
      m.t τ θ = E.t0 m.q (m.t τlo θlo) τ + θ * m.q τ θ - ∫ x in θlo..θ, m.q τ x := by
  exact tf_core E m hm hic
