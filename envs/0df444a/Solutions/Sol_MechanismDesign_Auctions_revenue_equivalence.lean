-- Prove2me | solution 1 for MechanismDesign.Auctions.revenue_equivalence
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T09:23:42.661247+00:00
-- url     : https://prove2.me/submissions/b8f818e9-ad3c-4bbc-95f4-c7c6f5584f66

import Mathlib
import Definitions.Def_MechanismDesign_Auctions_Model

open MeasureTheory


namespace MechanismDesign.Auctions

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

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {E : Environment ι}

lemma isIC_abs (m : DirectMechanism E) (hIC : m.IsIC) (i : ι) :
    ICabs (m.interimQ i) (m.interimT i) E.lo E.hi := fun x hx x' hx' => hIC i x hx x' hx'

lemma prior_ae_mem : ∀ᵐ θ ∂E.prior, θ ∈ E.typeSpace := by
  have hmeas : MeasurableSet E.typeSpace :=
    MeasurableSet.univ_pi (fun _ => measurableSet_Icc)
  exact (withDensity_absolutelyContinuous _ _).ae_le (ae_restrict_mem hmeas)

lemma update_mem {θ : ι → ℝ} (hθ : θ ∈ E.typeSpace) (i : ι) {x : ℝ}
    (hx : x ∈ Set.Icc E.lo E.hi) : Function.update θ i x ∈ E.typeSpace := by
  intro j _
  rcases eq_or_ne j i with rfl | hji
  · simpa using hx
  · rw [Function.update_of_ne hji]; exact hθ j trivial

lemma interimQ_nonneg (m : DirectMechanism E) (i : ι) {x : ℝ} (hx : x ∈ Set.Icc E.lo E.hi) :
    0 ≤ m.interimQ i x := by
  unfold DirectMechanism.interimQ
  apply integral_nonneg_of_ae
  filter_upwards [prior_ae_mem] with θ hθ
  exact m.q_nonneg _ (update_mem hθ i hx) i

theorem interimQ_monotone_core (m : DirectMechanism E) (hIC : m.IsIC) (i : ι) :
    MonotoneOn (m.interimQ i) (Set.Icc E.lo E.hi) := abs_mono (isIC_abs m hIC i)

theorem payoff_equivalence_core (m : DirectMechanism E) (hIC : m.IsIC) :
    ∀ i, ∀ x ∈ Set.Icc E.lo E.hi,
      m.interimU i x = m.interimU i E.lo + ∫ y in E.lo..x, m.interimQ i y := by
  intro i x hx
  exact abs_payoff (isIC_abs m hIC i) E.lo_lt_hi.le hx

theorem revenue_equivalence_core (m : DirectMechanism E) (hIC : m.IsIC) :
    ∀ i, ∀ x ∈ Set.Icc E.lo E.hi,
      m.interimT i x = m.interimT i E.lo + (x * m.interimQ i x - E.lo * m.interimQ i E.lo)
        - ∫ y in E.lo..x, m.interimQ i y := by
  intro i x hx
  have := payoff_equivalence_core m hIC i x hx
  unfold DirectMechanism.interimU at this
  linarith

lemma interimU_mono (m : DirectMechanism E) (hIC : m.IsIC) (i : ι) :
    MonotoneOn (m.interimU i) (Set.Icc E.lo E.hi) := by
  intro x hx y hy hxy
  have h := abs_sub (isIC_abs m hIC i) hx hy
  have := interimQ_nonneg m i hx
  unfold DirectMechanism.interimU
  nlinarith

theorem interimU_envelope_core (m : DirectMechanism E) (hIC : m.IsIC) (i : ι) :
    MonotoneOn (m.interimU i) (Set.Icc E.lo E.hi) ∧
    ConvexOn ℝ (Set.Icc E.lo E.hi) (m.interimU i) ∧
    {x | x ∈ Set.Ioo E.lo E.hi ∧ ¬ DifferentiableAt ℝ (m.interimU i) x}.Countable ∧
    ∀ x ∈ Set.Ioo E.lo E.hi, DifferentiableAt ℝ (m.interimU i) x →
      deriv (m.interimU i) x = m.interimQ i x := by
  have h := isIC_abs m hIC i
  have hab := E.lo_lt_hi.le
  refine ⟨interimU_mono m hIC i, ?_, ?_, ?_⟩
  · refine ⟨convex_Icc _ _, ?_⟩
    intro x hx y hy s t hs ht hst
    have hc : s • x + t • y ∈ Set.Icc E.lo E.hi := (convex_Icc _ _) hx hy hs ht hst
    have h1 := h x hx _ hc
    have h2 := h y hy _ hc
    simp only [smul_eq_mul, DirectMechanism.interimU] at *
    set c := s * x + t * y
    have e : c * m.interimQ i c - m.interimT i c
        = s * (x * m.interimQ i c - m.interimT i c) + t * (y * m.interimQ i c - m.interimT i c) := by
      have : s + t = 1 := hst
      simp only [c]; linear_combination (m.interimT i (s * x + t * y)) * this
    rw [e]
    nlinarith [mul_le_mul_of_nonneg_left h1 hs, mul_le_mul_of_nonneg_left h2 ht]
  · apply ((ext_mono h hab).countable_not_continuousAt).mono
    intro x ⟨hx, hnd⟩
    simp only [Set.mem_setOf_eq]
    intro hc
    exact hnd (abs_hasDerivAt h hab hx hc).differentiableAt
  · intro x hx hd
    have hxI : x ∈ Set.Icc E.lo E.hi := Set.Ioo_subset_Icc_self hx
    have hg : HasDerivAt (fun y => m.interimU i y - m.interimU i x - (y - x) * m.interimQ i x)
        (deriv (m.interimU i) x - m.interimQ i x) x := by
      have := ((hd.hasDerivAt.sub_const (m.interimU i x)).sub
        (((hasDerivAt_id x).sub_const x).mul_const (m.interimQ i x)))
      simp only [id, one_mul] at this
      exact this
    have hmin : IsLocalMin (fun y => m.interimU i y - m.interimU i x - (y - x) * m.interimQ i x) x := by
      filter_upwards [Icc_mem_nhds hx.1 hx.2] with y hy
      have := abs_sub h hxI hy
      simp only [DirectMechanism.interimU] at *
      simp only [sub_self, zero_mul, sub_zero]
      linarith
    have := hmin.hasDerivAt_eq_zero hg
    linarith

theorem ic_iff_core (m : DirectMechanism E) :
    m.IsIC ↔ ∀ i, MonotoneOn (m.interimQ i) (Set.Icc E.lo E.hi) ∧
      ∀ x ∈ Set.Icc E.lo E.hi,
        m.interimT i x = m.interimT i E.lo + (x * m.interimQ i x - E.lo * m.interimQ i E.lo)
          - ∫ y in E.lo..x, m.interimQ i y := by
  constructor
  · intro hIC i
    exact ⟨interimQ_monotone_core m hIC i, revenue_equivalence_core m hIC i⟩
  · intro H i x hx x' hx'
    obtain ⟨hm, hT⟩ := H i
    have hint : ∀ u ∈ Set.Icc E.lo E.hi, ∀ v ∈ Set.Icc E.lo E.hi,
        IntervalIntegrable (m.interimQ i) volume u v := by
      intro u hu v hv
      apply MonotoneOn.intervalIntegrable
      exact hm.mono (Set.uIcc_subset_Icc hu hv)
    have eT := hT x hx
    have eT' := hT x' hx'
    have hsplit : (∫ y in E.lo..x, m.interimQ i y) - ∫ y in E.lo..x', m.interimQ i y
        = ∫ y in x'..x, m.interimQ i y := by
      rw [intervalIntegral.integral_interval_sub_left (hint _ ⟨le_rfl, E.lo_lt_hi.le⟩ _ hx)
        (hint _ ⟨le_rfl, E.lo_lt_hi.le⟩ _ hx')]
    -- need (x - x') * Q x' ≤ ∫_{x'}^{x} Q
    have key : (x - x') * m.interimQ i x' ≤ ∫ y in x'..x, m.interimQ i y := by
      rcases le_total x' x with hle | hle
      · have : ∫ y in x'..x, m.interimQ i x' ≤ ∫ y in x'..x, m.interimQ i y := by
          apply intervalIntegral.integral_mono_on hle intervalIntegrable_const (hint _ hx' _ hx)
          intro y hy
          exact hm hx' ⟨le_trans hx'.1 hy.1, le_trans hy.2 hx.2⟩ hy.1
        simpa [mul_comm] using this
      · have : ∫ y in x..x', m.interimQ i y ≤ ∫ y in x..x', m.interimQ i x' := by
          apply intervalIntegral.integral_mono_on hle (hint _ hx _ hx') intervalIntegrable_const
          intro y hy
          exact hm ⟨le_trans hx.1 hy.1, le_trans hy.2 hx'.2⟩ hx' hy.2
        rw [intervalIntegral.integral_symm]
        simp at this
        nlinarith
    linarith

theorem ir_iff_core (m : DirectMechanism E) (hIC : m.IsIC) :
    m.IsIR ↔ ∀ i, m.interimT i E.lo ≤ E.lo * m.interimQ i E.lo := by
  have hlo : E.lo ∈ Set.Icc E.lo E.hi := ⟨le_rfl, E.lo_lt_hi.le⟩
  constructor
  · intro h i
    have := h i E.lo hlo
    unfold DirectMechanism.interimU at this; linarith
  · intro h i x hx
    have := interimU_mono m hIC i hlo hx hx.1
    have h0 : 0 ≤ m.interimU i E.lo := by unfold DirectMechanism.interimU; linarith [h i]
    linarith

def revMech (E : Environment ι)
    {S : ι → Type*} (alloc : ι → ((j : ι) → S j) → ℝ) (pay : ι → ((j : ι) → S j) → ℝ)
    (h_alloc_nonneg : ∀ s i, 0 ≤ alloc i s) (h_alloc_le_one : ∀ s i, alloc i s ≤ 1)
    (h_alloc_sum : ∀ s, ∑ i, alloc i s ≤ 1) (σ : (i : ι) → ℝ → S i) : DirectMechanism E where
  q := fun i θ => alloc i (fun j => σ j (θ j))
  t := fun i θ => pay i (fun j => σ j (θ j))
  q_nonneg := fun _ _ i => h_alloc_nonneg _ i
  q_le_one := fun _ _ i => h_alloc_le_one _ i
  sum_q_le_one := fun _ _ => h_alloc_sum _

lemma hupd {S : ι → Type*} (σ : (i : ι) → ℝ → S i) (i : ι) (x : ℝ) (θ : ι → ℝ) :
    (fun j => σ j (Function.update θ i x j)) = Function.update (fun j => σ j (θ j)) i (σ i x) := by
  funext j
  rcases eq_or_ne j i with rfl | h
  · simp
  · simp [Function.update_of_ne h]

lemma hσθ {S : ι → Type*} [∀ i, MeasurableSpace (S i)] (σ : (i : ι) → ℝ → S i)
    (hσ_meas : ∀ i, Measurable (σ i)) : Measurable (fun θ : ι → ℝ => fun j => σ j (θ j)) :=
  measurable_pi_lambda _ (fun j => (hσ_meas j).comp (measurable_pi_apply j))

lemma revQ (E : Environment ι)
    {S : ι → Type*} (alloc : ι → ((j : ι) → S j) → ℝ) (pay : ι → ((j : ι) → S j) → ℝ)
    (h0 : ∀ s i, 0 ≤ alloc i s) (h1 : ∀ s i, alloc i s ≤ 1)
    (h2 : ∀ s, ∑ i, alloc i s ≤ 1) (σ : (i : ι) → ℝ → S i) (i : ι) (x : ℝ) :
    (revMech E alloc pay h0 h1 h2 σ).interimQ i x
      = ∫ θ, alloc i (Function.update (fun j => σ j (θ j)) i (σ i x)) ∂E.prior := by
  unfold DirectMechanism.interimQ
  congr 1; funext θ; simp only [revMech]; rw [hupd]

lemma revT (E : Environment ι)
    {S : ι → Type*} (alloc : ι → ((j : ι) → S j) → ℝ) (pay : ι → ((j : ι) → S j) → ℝ)
    (h0 : ∀ s i, 0 ≤ alloc i s) (h1 : ∀ s i, alloc i s ≤ 1)
    (h2 : ∀ s, ∑ i, alloc i s ≤ 1) (σ : (i : ι) → ℝ → S i) (i : ι) (x : ℝ) :
    (revMech E alloc pay h0 h1 h2 σ).interimT i x
      = ∫ θ, pay i (Function.update (fun j => σ j (θ j)) i (σ i x)) ∂E.prior := by
  unfold DirectMechanism.interimT
  congr 1; funext θ; simp only [revMech]; rw [hupd]

theorem revelation_principle_core (E : Environment ι)
    {S : ι → Type*} [∀ i, MeasurableSpace (S i)]
    (alloc : ι → ((j : ι) → S j) → ℝ) (pay : ι → ((j : ι) → S j) → ℝ)
    (h_alloc_nonneg : ∀ s i, 0 ≤ alloc i s) (h_alloc_le_one : ∀ s i, alloc i s ≤ 1)
    (h_alloc_sum : ∀ s, ∑ i, alloc i s ≤ 1)
    (h_alloc_meas : ∀ i, Measurable (alloc i)) (h_pay_meas : ∀ i, Measurable (pay i))
    (σ : (i : ι) → ℝ → S i) (hσ_meas : ∀ i, Measurable (σ i))
    (h_pay_int : ∀ i, Integrable (fun θ => pay i (fun j => σ j (θ j))) E.prior)
    (h_dev_int : ∀ i, ∀ s : S i,
      Integrable (fun θ => pay i (Function.update (fun j => σ j (θ j)) i s)) E.prior)
    (h_BNE : ∀ i, ∀ x ∈ Set.Icc E.lo E.hi, ∀ s : S i,
      x * ∫ θ, alloc i (Function.update (fun j => σ j (θ j)) i s) ∂E.prior
          - ∫ θ, pay i (Function.update (fun j => σ j (θ j)) i s) ∂E.prior
        ≤ x * ∫ θ, alloc i (Function.update (fun j => σ j (θ j)) i (σ i x)) ∂E.prior
          - ∫ θ, pay i (Function.update (fun j => σ j (θ j)) i (σ i x)) ∂E.prior) :
    ∃ m : DirectMechanism E, m.WellDefined ∧ m.IsIC ∧
      ∀ θ ∈ E.typeSpace, ∀ i,
        m.q i θ = alloc i (fun j => σ j (θ j)) ∧ m.t i θ = pay i (fun j => σ j (θ j)) := by
  refine ⟨revMech E alloc pay h_alloc_nonneg h_alloc_le_one h_alloc_sum σ, ⟨?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · intro i; exact (h_alloc_meas i).comp (hσθ σ hσ_meas)
  · intro i; exact (h_pay_meas i).comp (hσθ σ hσ_meas)
  · intro i; exact h_pay_int i
  · intro i x _
    have : (fun θ => (revMech E alloc pay h_alloc_nonneg h_alloc_le_one h_alloc_sum σ).t i
        (Function.update θ i x)) = fun θ => pay i (Function.update (fun j => σ j (θ j)) i (σ i x)) := by
      funext θ; simp only [revMech]; rw [hupd]
    rw [this]; exact h_dev_int i (σ i x)
  · intro i x hx x' _
    rw [revQ, revQ, revT, revT]
    exact h_BNE i x hx (σ i x')
  · intro θ _ i; exact ⟨rfl, rfl⟩

end MechanismDesign.Auctions

open MechanismDesign.Auctions


theorem solution {ι : Type*} [Fintype ι] [DecidableEq ι] {E : Environment ι}
    (m : DirectMechanism E) (hIC : m.IsIC) :
    ∀ i, ∀ x ∈ Set.Icc E.lo E.hi,
      m.interimT i x = m.interimT i E.lo + (x * m.interimQ i x - E.lo * m.interimQ i E.lo)
        - ∫ y in E.lo..x, m.interimQ i y := by
  exact revenue_equivalence_core m hIC
