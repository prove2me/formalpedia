-- Prove2me | solution 1 for MechanismDesign.Screening.ic_iff
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T10:00:41.794419+00:00
-- url     : https://prove2.me/submissions/9ec8c6fb-8aca-4189-9640-3268aa066fad

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

end MechanismDesign.Screening

open MechanismDesign.Screening


theorem solution {θlo θhi : ℝ} (hlo : 0 ≤ θlo) (hlt : θlo < θhi)
    (m : DirectMechanism θlo θhi) :
    m.IsIC ↔
      (MonotoneOn m.q (Set.Icc θlo θhi) ∧
        ∀ θ ∈ Set.Icc θlo θhi,
          m.t θ = m.t θlo + (θ * m.q θ - θlo * m.q θlo) - ∫ x in θlo..θ, m.q x) := by
  exact ic_iff_core hlt m
