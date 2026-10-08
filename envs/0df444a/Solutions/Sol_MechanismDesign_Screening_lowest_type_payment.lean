-- Prove2me | solution 1 for MechanismDesign.Screening.lowest_type_payment
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T10:04:17.899752+00:00
-- url     : https://prove2.me/submissions/63937d82-e27f-4f7c-bb38-477575ee863c

import Mathlib
import Definitions.Def_MechanismDesign_Screening_Model

open MeasureTheory

namespace MechanismDesign.Screening

section Abstract
variable {Q T : ℝ → ℝ} {a b : ℝ}

def ICabs (Q T : ℝ → ℝ) (a b : ℝ) : Prop :=
  ∀ x ∈ Set.Icc a b, ∀ x' ∈ Set.Icc a b, x * Q x' - T x' ≤ x * Q x - T x

lemma abs_mono (h : ICabs Q T a b) : MonotoneOn Q (Set.Icc a b) := by
  intro x hx y hy hxy
  have h1 := h x hx y hy
  have h2 := h y hy x hx
  rcases eq_or_lt_of_le hxy with rfl | hlt
  · exact le_rfl
  · nlinarith

lemma abs_sub (h : ICabs Q T a b) {x y : ℝ} (hx : x ∈ Set.Icc a b) (hy : y ∈ Set.Icc a b) :
    (y - x) * Q x ≤ (y * Q y - T y) - (x * Q x - T x) := by
  have := h y hy x hx; nlinarith

lemma abs_lip (h : ICabs Q T a b) (hab : a ≤ b) :
    LipschitzOnWith (Real.toNNReal (max |Q a| |Q b|)) (fun x => x * Q x - T x) (Set.Icc a b) := by
  apply LipschitzOnWith.of_dist_le_mul
  intro x hx y hy
  have hm := abs_mono h
  have ha : a ∈ Set.Icc a b := ⟨le_rfl, hab⟩
  have hb : b ∈ Set.Icc a b := ⟨hab, le_rfl⟩
  have bx : |Q x| ≤ max |Q a| |Q b| := by
    have := hm ha hx hx.1; have := hm hx hb hx.2
    rw [abs_le]; constructor
    · have := le_max_left |Q a| |Q b|; have := neg_abs_le (Q a); linarith
    · have := le_max_right |Q a| |Q b|; have := le_abs_self (Q b); linarith
  have byy : |Q y| ≤ max |Q a| |Q b| := by
    have := hm ha hy hy.1; have := hm hy hb hy.2
    rw [abs_le]; constructor
    · have := le_max_left |Q a| |Q b|; have := neg_abs_le (Q a); linarith
    · have := le_max_right |Q a| |Q b|; have := le_abs_self (Q b); linarith
  have h1 := abs_sub h hx hy
  have h2 := abs_sub h hy hx
  rw [Real.dist_eq, Real.dist_eq, Real.coe_toNNReal _ (le_trans (abs_nonneg _) (le_max_left _ _))]
  set M := max |Q a| |Q b|
  rw [abs_le]
  rcases le_total x y with hxy | hxy
  · have e1 : |x - y| = y - x := by rw [abs_sub_comm]; exact abs_of_nonneg (by linarith)
    rw [e1]
    have := abs_le.1 bx; have := abs_le.1 byy
    constructor <;> nlinarith
  · have e1 : |x - y| = x - y := abs_of_nonneg (by linarith)
    rw [e1]
    have := abs_le.1 bx; have := abs_le.1 byy
    constructor <;> nlinarith

/-- monotone extension -/
noncomputable def ext (Q : ℝ → ℝ) (a b : ℝ) (hab : a ≤ b) : ℝ → ℝ :=
  fun x => Q (Set.projIcc a b hab x)

lemma ext_mono (h : ICabs Q T a b) (hab : a ≤ b) : Monotone (ext Q a b hab) := by
  intro x y hxy
  exact abs_mono h (Set.projIcc a b hab x).2 (Set.projIcc a b hab y).2
    (Set.monotone_projIcc hab hxy)

lemma ext_eq (hab : a ≤ b) {x : ℝ} (hx : x ∈ Set.Icc a b) : ext Q a b hab x = Q x := by
  simp [ext, Set.projIcc_of_mem hab hx]

lemma abs_hasDerivAt (h : ICabs Q T a b) (hab : a ≤ b) {x : ℝ} (hx : x ∈ Set.Ioo a b)
    (hc : ContinuousAt (ext Q a b hab) x) :
    HasDerivAt (fun x => x * Q x - T x) (Q x) x := by
  rw [hasDerivAt_iff_tendsto_slope]
  have hxI : x ∈ Set.Icc a b := Set.Ioo_subset_Icc_self hx
  have hev : ∀ᶠ y in nhdsWithin x {x}ᶜ, y ∈ Set.Icc a b :=
    nhdsWithin_le_nhds (Icc_mem_nhds hx.1 hx.2)
  rw [tendsto_iff_dist_tendsto_zero]
  have hlim : Filter.Tendsto (fun y => dist (ext Q a b hab y) (Q x)) (nhdsWithin x {x}ᶜ)
      (nhds 0) := by
    have : Filter.Tendsto (ext Q a b hab) (nhdsWithin x {x}ᶜ) (nhds (ext Q a b hab x)) :=
      hc.tendsto.mono_left nhdsWithin_le_nhds
    rw [ext_eq hab hxI] at this
    exact (tendsto_iff_dist_tendsto_zero).1 this
  apply squeeze_zero' (Filter.Eventually.of_forall (fun _ => dist_nonneg)) _ hlim
  filter_upwards [hev, self_mem_nhdsWithin] with y hy hyx
  rw [ext_eq hab hy, slope_def_field, Real.dist_eq, Real.dist_eq]
  have hyx' : y - x ≠ 0 := sub_ne_zero.2 hyx
  have h1 := abs_sub h hxI hy
  have h2 := abs_sub h hy hxI
  have hm := abs_mono h
  obtain ⟨s, hsD⟩ : ∃ s, (y * Q y - T y) - (x * Q x - T x) = s * (y - x) :=
    ⟨_, (div_mul_cancel₀ _ hyx').symm⟩
  rw [hsD, mul_div_cancel_right₀ _ hyx']
  rw [hsD] at h1
  have h2' : (x - y) * Q y ≤ -(s * (y - x)) := by linarith
  clear h2
  rcases lt_or_gt_of_ne hyx with hlt | hgt
  · have hQ := hm hy hxI hlt.le
    have b1 : s ≤ Q x := by nlinarith
    have b2 : Q y ≤ s := by nlinarith [h2']
    rw [abs_le]; constructor <;> rw [abs_of_nonpos (by linarith)] <;> linarith
  · have hQ := hm hxI hy hgt.le
    have b1 : Q x ≤ s := by nlinarith
    have b2 : s ≤ Q y := by nlinarith [h2']
    rw [abs_le]; constructor <;> rw [abs_of_nonneg (by linarith)] <;> linarith

lemma abs_payoff (h : ICabs Q T a b) (hab : a ≤ b) {x : ℝ} (hx : x ∈ Set.Icc a b) :
    x * Q x - T x = (a * Q a - T a) + ∫ y in a..x, Q y := by
  have hsub : Set.Icc a x ⊆ Set.Icc a b := Set.Icc_subset_Icc le_rfl hx.2
  have key := integral_eq_of_hasDerivAt_off_countable_of_le (fun x => x * Q x - T x) Q hx.1
    (ext_mono h hab).countable_not_continuousAt
    ((abs_lip h hab).continuousOn.mono hsub)
    (fun y hy => abs_hasDerivAt h hab ⟨hy.1.1, lt_of_lt_of_le hy.1.2 hx.2⟩ (by
      by_contra hc; exact hy.2 hc))
    (by
      apply MonotoneOn.intervalIntegrable
      rw [Set.uIcc_of_le hx.1]; exact (abs_mono h).mono hsub)
  rw [key]; ring

end Abstract

variable {θlo θhi : ℝ}

lemma isIC_abs (m : DirectMechanism θlo θhi) (hIC : m.IsIC) : ICabs m.q m.t θlo θhi :=
  fun x hx x' hx' => hIC x hx x' hx'

theorem ic_q_monotone_core (m : DirectMechanism θlo θhi) (hic : m.IsIC) :
    MonotoneOn m.q (Set.Icc θlo θhi) := abs_mono (isIC_abs m hic)

theorem payoff_equivalence_core (hlt : θlo < θhi) (m : DirectMechanism θlo θhi) (hic : m.IsIC) :
    ∀ θ ∈ Set.Icc θlo θhi, m.u θ = m.u θlo + ∫ x in θlo..θ, m.q x := by
  intro x hx
  exact abs_payoff (isIC_abs m hic) hlt.le hx

theorem revenue_equivalence_core (hlt : θlo < θhi) (m : DirectMechanism θlo θhi) (hic : m.IsIC) :
    ∀ θ ∈ Set.Icc θlo θhi,
      m.t θ = m.t θlo + (θ * m.q θ - θlo * m.q θlo) - ∫ x in θlo..θ, m.q x := by
  intro x hx
  have := payoff_equivalence_core hlt m hic x hx
  unfold DirectMechanism.u at this
  linarith

lemma u_mono (m : DirectMechanism θlo θhi) (hIC : m.IsIC) :
    MonotoneOn m.u (Set.Icc θlo θhi) := by
  intro x hx y hy hxy
  have h := abs_sub (isIC_abs m hIC) hx hy
  have := (m.q_mem x hx).1
  unfold DirectMechanism.u
  nlinarith

theorem envelope_core (hlt : θlo < θhi) (m : DirectMechanism θlo θhi) (hic : m.IsIC) :
    MonotoneOn m.u (Set.Icc θlo θhi) ∧ ConvexOn ℝ (Set.Icc θlo θhi) m.u ∧
      {θ ∈ Set.Ioo θlo θhi | ¬ DifferentiableAt ℝ m.u θ}.Countable ∧
      ∀ θ ∈ Set.Ioo θlo θhi, DifferentiableAt ℝ m.u θ → deriv m.u θ = m.q θ := by
  have h := isIC_abs m hic
  have hab := hlt.le
  refine ⟨u_mono m hic, ?_, ?_, ?_⟩
  · refine ⟨convex_Icc _ _, ?_⟩
    intro x hx y hy s t hs ht hst
    have hc : s • x + t • y ∈ Set.Icc θlo θhi := (convex_Icc _ _) hx hy hs ht hst
    have h1 := h x hx _ hc
    have h2 := h y hy _ hc
    simp only [smul_eq_mul, DirectMechanism.u] at *
    set c := s * x + t * y
    have e : c * m.q c - m.t c
        = s * (x * m.q c - m.t c) + t * (y * m.q c - m.t c) := by
      have : s + t = 1 := hst
      simp only [c]; linear_combination (m.t (s * x + t * y)) * this
    rw [e]
    nlinarith [mul_le_mul_of_nonneg_left h1 hs, mul_le_mul_of_nonneg_left h2 ht]
  · apply ((ext_mono h hab).countable_not_continuousAt).mono
    intro x ⟨hx, hnd⟩
    simp only [Set.mem_setOf_eq]
    intro hc
    exact hnd (abs_hasDerivAt h hab hx hc).differentiableAt
  · intro x hx hd
    have hxI : x ∈ Set.Icc θlo θhi := Set.Ioo_subset_Icc_self hx
    have hg : HasDerivAt (fun y => m.u y - m.u x - (y - x) * m.q x)
        (deriv m.u x - m.q x) x := by
      have := ((hd.hasDerivAt.sub_const (m.u x)).sub
        (((hasDerivAt_id x).sub_const x).mul_const (m.q x)))
      simp only [id, one_mul] at this
      exact this
    have hmin : IsLocalMin (fun y => m.u y - m.u x - (y - x) * m.q x) x := by
      filter_upwards [Icc_mem_nhds hx.1 hx.2] with y hy
      have := abs_sub h hxI hy
      simp only [DirectMechanism.u] at *
      simp only [sub_self, zero_mul, sub_zero]
      linarith
    have := hmin.hasDerivAt_eq_zero hg
    linarith

theorem ic_iff_core (hlt : θlo < θhi) (m : DirectMechanism θlo θhi) :
    m.IsIC ↔
      (MonotoneOn m.q (Set.Icc θlo θhi) ∧
        ∀ θ ∈ Set.Icc θlo θhi,
          m.t θ = m.t θlo + (θ * m.q θ - θlo * m.q θlo) - ∫ x in θlo..θ, m.q x) := by
  constructor
  · intro hIC
    exact ⟨ic_q_monotone_core m hIC, revenue_equivalence_core hlt m hIC⟩
  · rintro ⟨hm, hT⟩ x hx x' hx'
    have hint : ∀ u ∈ Set.Icc θlo θhi, ∀ v ∈ Set.Icc θlo θhi,
        IntervalIntegrable m.q volume u v := by
      intro u hu v hv
      apply MonotoneOn.intervalIntegrable
      exact hm.mono (Set.uIcc_subset_Icc hu hv)
    have eT := hT x hx
    have eT' := hT x' hx'
    have hsplit : (∫ y in θlo..x, m.q y) - ∫ y in θlo..x', m.q y
        = ∫ y in x'..x, m.q y := by
      rw [intervalIntegral.integral_interval_sub_left (hint _ ⟨le_rfl, hlt.le⟩ _ hx)
        (hint _ ⟨le_rfl, hlt.le⟩ _ hx')]
    have key : (x - x') * m.q x' ≤ ∫ y in x'..x, m.q y := by
      rcases le_total x' x with hle | hle
      · have : ∫ y in x'..x, m.q x' ≤ ∫ y in x'..x, m.q y := by
          apply intervalIntegral.integral_mono_on hle intervalIntegrable_const (hint _ hx' _ hx)
          intro y hy
          exact hm hx' ⟨le_trans hx'.1 hy.1, le_trans hy.2 hx.2⟩ hy.1
        simpa [mul_comm] using this
      · have : ∫ y in x..x', m.q y ≤ ∫ y in x..x', m.q x' := by
          apply intervalIntegral.integral_mono_on hle (hint _ hx _ hx') intervalIntegrable_const
          intro y hy
          exact hm ⟨le_trans hx.1 hy.1, le_trans hy.2 hx'.2⟩ hx' hy.2
        rw [intervalIntegral.integral_symm]
        simp at this
        nlinarith
    unfold DirectMechanism.u
    linarith

theorem ir_iff_core (hlt : θlo < θhi) (m : DirectMechanism θlo θhi) (hic : m.IsIC) :
    (m.IsIR ↔ 0 ≤ m.u θlo) ∧ (m.IsIR ↔ m.t θlo ≤ θlo * m.q θlo) := by
  have hlo : θlo ∈ Set.Icc θlo θhi := ⟨le_rfl, hlt.le⟩
  have h1 : m.IsIR ↔ 0 ≤ m.u θlo := by
    constructor
    · intro h; exact h θlo hlo
    · intro h x hx
      exact le_trans h (u_mono m hic hlo hx hx.1)
  refine ⟨h1, ?_⟩
  rw [h1]; unfold DirectMechanism.u; constructor <;> intro h <;> linarith

theorem revelation_principle_core (Γ : Mechanism) (σ : ℝ → Γ.S)
    (hσ : Γ.IsOptimalStrategy θlo θhi σ) :
    ∃ (m : DirectMechanism θlo θhi) (σ' : ℝ → ℝ), m.IsOptimalStrategy σ' ∧
      (∀ θ ∈ Set.Icc θlo θhi, σ' θ = θ) ∧
      (∀ θ ∈ Set.Icc θlo θhi, m.q θ = Γ.prob (σ θ) ∧ m.t θ = Γ.pay (σ θ)) := by
  refine ⟨⟨fun θ => Γ.prob (σ θ), fun θ => Γ.pay (σ θ), fun θ _ => Γ.prob_mem _⟩, id,
    ?_, fun _ _ => rfl, fun _ _ => ⟨rfl, rfl⟩⟩
  intro θ hθ
  exact ⟨hθ, fun θ' _ => hσ θ hθ (σ θ')⟩


variable {θlo θhi : ℝ}

lemma ae_ne_pt (p : ℝ) : ∀ᵐ x ∂(volume : Measure ℝ), x ≠ p := by
  rw [ae_iff]; simp

lemma ii_bdd_mul {a b : ℝ} (hab : a ≤ b) {f g : ℝ → ℝ} (hf : IntervalIntegrable f volume a b)
    (hg : AEStronglyMeasurable g (volume.restrict (Set.Ioc a b))) (C : ℝ)
    (hC : ∀ x ∈ Set.Icc a b, |g x| ≤ C) :
    IntervalIntegrable (fun x => g x * f x) volume a b := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab] at hf ⊢
  refine Integrable.bdd_mul (c := C) hf hg ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
  simpa using hC x (Set.Ioc_subset_Icc_self hx)

lemma t_formula_meas (hlt : θlo < θhi) (m : DirectMechanism θlo θhi) (hic : m.IsIC) :
    AEStronglyMeasurable m.t (volume.restrict (Set.Ioc θlo θhi)) := by
  have h := isIC_abs m hic
  have hab := hlt.le
  set e := ext m.q θlo θhi hab
  have hem : Monotone e := ext_mono h hab
  have hcont : Continuous (fun θ => ∫ x in θlo..θ, e x) :=
    intervalIntegral.continuous_primitive (fun a b => hem.intervalIntegrable) θlo
  have hmeas : Measurable (fun θ => m.t θlo + (θ * e θ - θlo * m.q θlo) - ∫ x in θlo..θ, e x) := by
    have := hem.measurable
    fun_prop
  refine (hmeas.aestronglyMeasurable).congr ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with θ hθ
  have hθ' := Set.Ioc_subset_Icc_self hθ
  rw [revenue_equivalence_core hlt m hic θ hθ']
  have e1 : e θ = m.q θ := ext_eq hab hθ'
  have e2 : ∫ x in θlo..θ, e x = ∫ x in θlo..θ, m.q x := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [Set.uIcc_of_le hθ'.1] at hx
    exact ext_eq hab ⟨hx.1, hx.2.trans hθ'.2⟩
  rw [e1, e2]

lemma int_q_bounds (hlt : θlo < θhi) (m : DirectMechanism θlo θhi) (hic : m.IsIC)
    {θ : ℝ} (hθ : θ ∈ Set.Icc θlo θhi) :
    0 ≤ ∫ x in θlo..θ, m.q x ∧ ∫ x in θlo..θ, m.q x ≤ θ - θlo := by
  have hsub : Set.uIcc θlo θ ⊆ Set.Icc θlo θhi := by
    rw [Set.uIcc_of_le hθ.1]; exact Set.Icc_subset_Icc le_rfl hθ.2
  have hii : IntervalIntegrable m.q volume θlo θ :=
    ((ic_q_monotone_core m hic).mono hsub).intervalIntegrable
  constructor
  · apply intervalIntegral.integral_nonneg hθ.1
    intro x hx; exact (m.q_mem x (hsub (by rw [Set.uIcc_of_le hθ.1]; exact hx))).1
  · have : ∫ x in θlo..θ, m.q x ≤ ∫ x in θlo..θ, (1:ℝ) := by
      apply intervalIntegral.integral_mono_on hθ.1 hii intervalIntegrable_const
      intro x hx; exact (m.q_mem x (hsub (by rw [Set.uIcc_of_le hθ.1]; exact hx))).2
    simpa using this

lemma tf_integrable (D : TypeDistribution θlo θhi) (m : DirectMechanism θlo θhi) (hic : m.IsIC) :
    IntervalIntegrable (fun θ => m.t θ * D.f θ) volume θlo θhi := by
  have hlt := D.lo_lt_hi
  have hlo := D.lo_nonneg
  refine ii_bdd_mul hlt.le D.f_integrable (t_formula_meas hlt m hic) (2 * |m.t θlo| + 3 * θhi) ?_
  intro θ hθ
  rw [revenue_equivalence_core hlt m hic θ hθ]
  obtain ⟨i1, i2⟩ := int_q_bounds hlt m hic hθ
  have q1 := m.q_mem θ hθ
  have q2 := m.q_mem θlo ⟨le_rfl, hlt.le⟩
  have a1 : 0 ≤ θ * m.q θ := mul_nonneg (hlo.trans hθ.1) q1.1
  have a2 : θ * m.q θ ≤ θhi := by nlinarith [hθ.2, q1.2]
  have a3 : 0 ≤ θlo * m.q θlo := mul_nonneg hlo q2.1
  have a4 : θlo * m.q θlo ≤ θhi := by nlinarith [q2.2]
  rw [abs_le]; constructor
  · have := neg_abs_le (m.t θlo); have := abs_nonneg (m.t θlo); nlinarith [hθ.1, hθ.2]
  · have := le_abs_self (m.t θlo); have := abs_nonneg (m.t θlo); nlinarith [hθ.1, hθ.2]

theorem lowest_type_payment_core (D : TypeDistribution θlo θhi)
    (m : DirectMechanism θlo θhi) (hic : m.IsIC) (hir : m.IsIR)
    (hopt : ∀ m' : DirectMechanism θlo θhi, m'.IsIC → m'.IsIR →
      expectedRevenue D m' ≤ expectedRevenue D m) :
    m.t θlo = θlo * m.q θlo := by
  have hlt := D.lo_lt_hi
  have hlo : θlo ∈ Set.Icc θlo θhi := ⟨le_rfl, hlt.le⟩
  set δ := θlo * m.q θlo - m.t θlo with hδ
  have hδ0 : 0 ≤ δ := by have := hir θlo hlo; unfold DirectMechanism.u at this; linarith
  let m' : DirectMechanism θlo θhi := ⟨m.q, fun θ => m.t θ + δ, m.q_mem⟩
  have hic' : m'.IsIC := by
    intro θ hθ θ' hθ'
    have := hic θ hθ θ' hθ'
    simp only [m', DirectMechanism.u] at this ⊢; linarith
  have hir' : m'.IsIR := by
    intro θ hθ
    have := u_mono m hic hlo hθ hθ.1
    simp only [m', DirectMechanism.u] at this ⊢; linarith
  have h := hopt m' hic' hir'
  unfold expectedRevenue at h
  have e : ∫ θ in θlo..θhi, m'.t θ * D.f θ
      = (∫ θ in θlo..θhi, m.t θ * D.f θ) + δ * ∫ θ in θlo..θhi, D.f θ := by
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_add
      (tf_integrable D m hic) (D.f_integrable.const_mul δ)]
    congr 1; funext θ; simp only [m']; ring
  rw [e, D.f_total] at h
  linarith

/-- threshold structure of a monotone 0/1 function -/
lemma threshold_of_mono01 {a b : ℝ} (hab : a ≤ b) (c : ℝ → ℝ) (hmono : MonotoneOn c (Set.Icc a b))
    (h01 : ∀ x ∈ Set.Icc a b, c x = 0 ∨ c x = 1) :
    ∃ p ∈ Set.Icc a b, ∀ x ∈ Set.Icc a b, x ≠ p → c x = if p < x then 1 else 0 := by
  by_cases hS : ∃ x ∈ Set.Icc a b, c x = 1
  · set S := {x | x ∈ Set.Icc a b ∧ c x = 1}
    obtain ⟨x0, hx0, hcx0⟩ := hS
    have hne : S.Nonempty := ⟨x0, hx0, hcx0⟩
    have hbdd : BddBelow S := ⟨a, fun x hx => hx.1.1⟩
    refine ⟨sInf S, ⟨le_csInf hne (fun x hx => hx.1.1), (csInf_le hbdd ⟨hx0, hcx0⟩).trans hx0.2⟩, ?_⟩
    intro x hx hxp
    split_ifs with hpx
    · obtain ⟨y, hy, hyx⟩ := exists_lt_of_csInf_lt hne hpx
      have := hmono hy.1 hx hyx.le
      rcases h01 x hx with h | h
      · rw [hy.2] at this; linarith
      · exact h
    · have hxlt : x < sInf S := lt_of_le_of_ne (not_lt.1 hpx) hxp
      rcases h01 x hx with h | h
      · exact h
      · exact absurd (csInf_le hbdd ⟨hx, h⟩) (not_le.2 hxlt)
  · push_neg at hS
    refine ⟨b, ⟨hab, le_rfl⟩, ?_⟩
    intro x hx hxb
    have : ¬ b < x := not_lt.2 hx.2
    rw [if_neg this]
    rcases h01 x hx with h | h
    · exact h
    · exact absurd h (hS x hx)

lemma int_thr {a p θ : ℝ} (hp : a ≤ p) (hθ : a ≤ θ) :
    ∫ x in a..θ, (if p < x then (1:ℝ) else 0) = if p < θ then θ - p else 0 := by
  split_ifs with hpθ
  · rw [← intervalIntegral.integral_add_adjacent_intervals (b := p)]
    · have h1 : ∫ x in a..p, (if p < x then (1:ℝ) else 0) = 0 := by
        rw [intervalIntegral.integral_congr (g := fun _ => (0:ℝ))]
        · simp
        intro x hx; rw [Set.uIcc_of_le hp] at hx; simp [not_lt.2 hx.2]
      have h2 : ∫ x in p..θ, (if p < x then (1:ℝ) else 0) = θ - p := by
        rw [intervalIntegral.integral_congr_ae (g := fun _ => (1:ℝ))]
        · simp
        refine Filter.Eventually.of_forall (fun x hx => ?_)
        rw [Set.uIoc_of_le hpθ.le] at hx; simp [hx.1]
      rw [h1, h2]; ring
    · apply Monotone.intervalIntegrable
      intro x y hxy; dsimp only
      by_cases h1 : p < x
      · have : p < y := h1.trans_le hxy
        simp [h1, this]
      · by_cases h2 : p < y <;> simp [h1, h2]
    · apply Monotone.intervalIntegrable
      intro x y hxy; dsimp only
      by_cases h1 : p < x
      · have : p < y := h1.trans_le hxy
        simp [h1, this]
      · by_cases h2 : p < y <;> simp [h1, h2]
  · rw [intervalIntegral.integral_congr (g := fun _ => (0:ℝ))]
    · simp
    intro x hx; rw [Set.uIcc_of_le hθ] at hx
    simp only
    rw [if_neg]; intro h; exact hpθ (h.trans_le hx.2)

lemma ite_meas (p v : ℝ) : Measurable (fun θ : ℝ => if p < θ then v else 0) :=
  Measurable.ite measurableSet_Ioi measurable_const measurable_const

lemma thr_ii (D : TypeDistribution θlo θhi) (p v : ℝ) :
    IntervalIntegrable (fun θ => (if p < θ then v else 0) * D.f θ) volume θlo θhi :=
  ii_bdd_mul D.lo_lt_hi.le D.f_integrable (ite_meas p v).aestronglyMeasurable (|v|)
    (fun x _ => by split_ifs <;> simp)

lemma thr_integral (D : TypeDistribution θlo θhi) {p : ℝ} (hp : p ∈ Set.Icc θlo θhi) :
    ∫ θ in θlo..θhi, (if p < θ then p else 0) * D.f θ = p * (1 - D.F p) := by
  have s1 : Set.uIcc θlo p ⊆ Set.uIcc θlo θhi := by
    rw [Set.uIcc_of_le hp.1, Set.uIcc_of_le (hp.1.trans hp.2)]
    exact Set.Icc_subset_Icc le_rfl hp.2
  have s2 : Set.uIcc p θhi ⊆ Set.uIcc θlo θhi := by
    rw [Set.uIcc_of_le hp.2, Set.uIcc_of_le (hp.1.trans hp.2)]
    exact Set.Icc_subset_Icc hp.1 le_rfl
  have hf1 : IntervalIntegrable D.f volume θlo p := D.f_integrable.mono_set s1
  have hf2 : IntervalIntegrable D.f volume p θhi := D.f_integrable.mono_set s2
  have htot : ∫ x in θlo..θhi, D.f x = (∫ x in θlo..p, D.f x) + ∫ x in p..θhi, D.f x :=
    (intervalIntegral.integral_add_adjacent_intervals hf1 hf2).symm
  have hI := thr_ii D p p
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := p) (hI.mono_set s1) (hI.mono_set s2)]
  have h1 : ∫ θ in θlo..p, (if p < θ then p else 0) * D.f θ = 0 := by
    rw [intervalIntegral.integral_congr (g := fun _ => (0:ℝ))]
    · simp
    intro x hx; rw [Set.uIcc_of_le hp.1] at hx; simp [not_lt.2 hx.2]
  have h2 : ∫ θ in p..θhi, (if p < θ then p else 0) * D.f θ = p * ∫ θ in p..θhi, D.f θ := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr_ae
    refine Filter.Eventually.of_forall (fun x hx => ?_)
    rw [Set.uIoc_of_le hp.2] at hx; simp [hx.1]
  rw [h1, h2, D.F_eq p hp]
  rw [D.f_total] at htot
  rw [zero_add]; congr 1; linarith

theorem postedPrice_IC (p : ℝ) : (postedPrice θlo θhi p).IsIC := by
  intro θ _ θ' _
  simp only [postedPrice, DirectMechanism.u]
  split_ifs <;> nlinarith

theorem postedPrice_IR (p : ℝ) : (postedPrice θlo θhi p).IsIR := by
  intro θ _
  simp only [postedPrice, DirectMechanism.u]
  split_ifs <;> nlinarith

end MechanismDesign.Screening

open MechanismDesign.Screening


theorem solution {θlo θhi : ℝ} (D : TypeDistribution θlo θhi)
    (m : DirectMechanism θlo θhi) (hic : m.IsIC) (hir : m.IsIR)
    (hopt : ∀ m' : DirectMechanism θlo θhi, m'.IsIC → m'.IsIR →
      expectedRevenue D m' ≤ expectedRevenue D m) :
    m.t θlo = θlo * m.q θlo := by
  exact lowest_type_payment_core D m hic hir hopt
