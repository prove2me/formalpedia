-- Prove2me | solution 1 for MechanismDesign.Auctions.revenue_eq_virtual_surplus
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T09:31:53.821929+00:00
-- url     : https://prove2.me/submissions/c5373b06-cd41-41a9-a5fe-622abda9e2e2

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


lemma ofReal_max0 (y : ℝ) : ENNReal.ofReal y = ENNReal.ofReal (max y 0) := by
  rcases le_total y 0 with h | h
  · rw [max_eq_right h, ENNReal.ofReal_of_nonpos h, ENNReal.ofReal_zero]
  · rw [max_eq_left h]

lemma lint_prod {ι : Type*} [Fintype ι] (ν : ι → Measure ℝ) [∀ j, SigmaFinite (ν j)]
    (g : ι → ℝ → ℝ) (hg : ∀ j, Integrable (g j) (ν j)) :
    ∫⁻ θ, ∏ j, ENNReal.ofReal (g j (θ j)) ∂(Measure.pi ν)
      = ∏ j, ∫⁻ x, ENNReal.ofReal (g j x) ∂(ν j) := by
  have hp : ∀ j, Integrable (fun x => max (g j x) 0) (ν j) := fun j => (hg j).pos_part
  have e1 : (fun θ : ι → ℝ => ∏ j, ENNReal.ofReal (g j (θ j)))
      = fun θ => ENNReal.ofReal (∏ j, max (g j (θ j)) 0) := by
    funext θ
    rw [ENNReal.ofReal_prod_of_nonneg (fun j _ => le_max_right _ _)]
    exact Finset.prod_congr rfl (fun j _ => ofReal_max0 _)
  rw [e1]
  rw [← ofReal_integral_eq_lintegral_ofReal (Integrable.fintype_prod (f := fun j x => max (g j x) 0) hp)
    (Filter.Eventually.of_forall (fun θ => Finset.prod_nonneg (fun j _ => le_max_right _ _)))]
  rw [integral_fintype_prod_eq_prod (fun j x => max (g j x) 0)]
  rw [ENNReal.ofReal_prod_of_nonneg (s := Finset.univ) (f := fun j => ∫ x, max (g j x) 0 ∂ν j)
    (fun j _ => integral_nonneg (fun x => le_max_right (g j x) 0))]
  congr 1; funext j
  rw [ofReal_integral_eq_lintegral_ofReal (hp j) (Filter.Eventually.of_forall (fun x => le_max_right _ _))]
  exact lintegral_congr (fun x => (ofReal_max0 _).symm)


/-- marginal law of buyer `i` -/
noncomputable def Environment.marg (E : Environment ι) (i : ι) : Measure ℝ :=
  (volume.restrict (Set.Icc E.lo E.hi)).withDensity (fun x => ENNReal.ofReal (E.f i x))

lemma f_integrableOn (E : Environment ι) (i : ι) : IntegrableOn (E.f i) (Set.Icc E.lo E.hi) := by
  rw [integrableOn_Icc_iff_integrableOn_Ioc]
  exact (intervalIntegrable_iff_integrableOn_Ioc_of_le E.lo_lt_hi.le).1 (E.f_intervalIntegrable i)

lemma marg_apply (E : Environment ι) (i : ι) {s : Set ℝ} (hs : MeasurableSet s) :
    E.marg i s = ∫⁻ x, ENNReal.ofReal (E.f i x) ∂(volume.restrict (s ∩ Set.Icc E.lo E.hi)) := by
  rw [Environment.marg, withDensity_apply _ hs, Measure.restrict_restrict hs]

lemma marg_univ (E : Environment ι) (i : ι) : E.marg i Set.univ = 1 := by
  rw [marg_apply E i MeasurableSet.univ, Set.univ_inter,
    ← ofReal_integral_eq_lintegral_ofReal (f_integrableOn E i)]
  · rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le E.lo_lt_hi.le,
      E.f_integral i, ENNReal.ofReal_one]
  · filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
    exact (E.f_pos i x hx).le

instance marg_prob (E : Environment ι) (i : ι) : IsProbabilityMeasure (E.marg i) :=
  ⟨marg_univ E i⟩

lemma prior_eq_pi (E : Environment ι) : E.prior = Measure.pi (fun i => E.marg i) := by
  symm
  apply Measure.pi_eq
  intro s hs
  have hTS : MeasurableSet E.typeSpace := MeasurableSet.univ_pi (fun _ => measurableSet_Icc)
  rw [Environment.prior, withDensity_apply _ (MeasurableSet.univ_pi hs),
    Measure.restrict_restrict (MeasurableSet.univ_pi hs), Environment.typeSpace,
    ← Set.pi_inter_distrib, volume_pi, Measure.restrict_pi_pi]
  rw [lint_prod (fun j => volume.restrict (s j ∩ Set.Icc E.lo E.hi)) (fun j => E.f j)
    (fun j => (f_integrableOn E j).mono_set Set.inter_subset_right)]
  congr 1; funext j
  rw [marg_apply E j (hs j)]

instance prior_prob (E : Environment ι) : IsProbabilityMeasure E.prior := by
  rw [prior_eq_pi]; infer_instance

/-- the update map is measure preserving -/
lemma update_mp (E : Environment ι) (i : ι) :
    MeasurePreserving (fun p : (ι → ℝ) × ℝ => Function.update p.1 i p.2)
      (E.prior.prod (E.marg i)) E.prior := by
  refine ⟨measurable_update', ?_⟩
  rw [prior_eq_pi]
  symm
  apply Measure.pi_eq
  intro s hs
  rw [Measure.map_apply measurable_update' (MeasurableSet.univ_pi hs)]
  have hpre : (fun p : (ι → ℝ) × ℝ => Function.update p.1 i p.2) ⁻¹' (Set.univ.pi s)
      = (Set.univ.pi (Function.update s i Set.univ)) ×ˢ s i := by
    ext ⟨θ, x⟩
    simp only [Set.mem_preimage, Set.mem_univ_pi, Set.mem_prod]
    constructor
    · intro h
      refine ⟨fun j => ?_, by simpa using h i⟩
      rcases eq_or_ne j i with rfl | hji
      · simp
      · have := h j; rw [Function.update_of_ne hji] at this ⊢; exact this
    · rintro ⟨h1, h2⟩ j
      rcases eq_or_ne j i with rfl | hji
      · simpa using h2
      · have := h1 j; rw [Function.update_of_ne hji] at this ⊢; exact this
  rw [hpre, Measure.prod_prod, Measure.pi_pi]
  rw [← Finset.mul_prod_erase Finset.univ (fun j => E.marg j (s j)) (Finset.mem_univ i),
    ← Finset.mul_prod_erase Finset.univ (fun j => E.marg j (Function.update s i Set.univ j))
      (Finset.mem_univ i)]
  simp only [Function.update_self, measure_univ, one_mul]
  rw [mul_comm]
  congr 1
  apply Finset.prod_congr rfl
  intro j hj
  have : j ≠ i := Finset.ne_of_mem_erase hj
  rw [Function.update_of_ne this]

/-- Fubini along buyer `i`. -/
lemma integral_interim (E : Environment ι) (i : ι) {g : (ι → ℝ) → ℝ} (hg : Integrable g E.prior) :
    ∫ θ, g θ ∂E.prior = ∫ x, (∫ θ, g (Function.update θ i x) ∂E.prior) ∂(E.marg i) := by
  have mp := update_mp E i
  have hgi : Integrable (fun p : (ι → ℝ) × ℝ => g (Function.update p.1 i p.2))
      (E.prior.prod (E.marg i)) :=
    (mp.integrable_comp hg.aestronglyMeasurable).2 hg
  conv_lhs => rw [← mp.map_eq]
  rw [integral_map mp.measurable.aemeasurable (by rw [mp.map_eq]; exact hg.aestronglyMeasurable)]
  exact integral_prod_symm _ hgi

lemma integral_marg (E : Environment ι) (i : ι) (h : ℝ → ℝ) :
    ∫ x, h x ∂(E.marg i) = ∫ x in E.lo..E.hi, h x * E.f i x := by
  rw [Environment.marg, integral_withDensity_eq_integral_toReal_smul
    (f := fun x => ENNReal.ofReal (E.f i x)) (E.f_measurable i).ennreal_ofReal
    (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  rw [intervalIntegral.integral_of_le E.lo_lt_hi.le, ← integral_Icc_eq_integral_Ioc]
  apply setIntegral_congr_fun measurableSet_Icc
  intro x hx
  simp only [smul_eq_mul]
  rw [ENNReal.toReal_ofReal (E.f_pos i x hx).le, mul_comm]


/-- add a constant to buyer `i0`'s payment -/
def shiftMech (m : DirectMechanism E) (i0 : ι) (c : ℝ) : DirectMechanism E where
  q := m.q
  t := fun j θ => m.t j θ + (if j = i0 then c else 0)
  q_nonneg := m.q_nonneg
  q_le_one := m.q_le_one
  sum_q_le_one := m.sum_q_le_one

lemma shift_T (m : DirectMechanism E) (hwd : m.WellDefined) (i0 : ι) (c : ℝ) (j : ι)
    {x : ℝ} (hx : x ∈ Set.Icc E.lo E.hi) :
    (shiftMech m i0 c).interimT j x = m.interimT j x + (if j = i0 then c else 0) := by
  unfold DirectMechanism.interimT
  simp only [shiftMech]
  rw [integral_add (hwd.t_section_integrable j x hx) (integrable_const _)]
  simp

lemma shift_Q (m : DirectMechanism E) (i0 : ι) (c : ℝ) :
    (shiftMech m i0 c).interimQ = m.interimQ := rfl

lemma shift_wd (m : DirectMechanism E) (hwd : m.WellDefined) (i0 : ι) (c : ℝ) :
    (shiftMech m i0 c).WellDefined := by
  refine ⟨hwd.q_measurable, fun j => (hwd.t_measurable j).add_const _,
    fun j => (hwd.t_integrable j).add (integrable_const _),
    fun j x hx => (hwd.t_section_integrable j x hx).add (integrable_const _)⟩

lemma shift_rev (m : DirectMechanism E) (hwd : m.WellDefined) (i0 : ι) (c : ℝ) :
    (shiftMech m i0 c).revenue = m.revenue + c := by
  unfold DirectMechanism.revenue
  simp only [shiftMech]
  rw [Finset.sum_congr rfl (fun j _ => integral_add (hwd.t_integrable j) (integrable_const _))]
  simp [Finset.sum_add_distrib]

theorem lowest_type_binding_core (m : DirectMechanism E) (hm : m.Admissible)
    (hopt : ∀ m' : DirectMechanism E, m'.Admissible → m'.revenue ≤ m.revenue) :
    ∀ i, m.interimT i E.lo = E.lo * m.interimQ i E.lo := by
  obtain ⟨hwd, hIC, hIR⟩ := hm
  have hlo : E.lo ∈ Set.Icc E.lo E.hi := ⟨le_rfl, E.lo_lt_hi.le⟩
  intro i0
  have hle := (ir_iff_core m hIC).1 hIR i0
  by_contra hne
  set c := E.lo * m.interimQ i0 E.lo - m.interimT i0 E.lo with hc
  have cpos : 0 < c := by
    rcases lt_or_eq_of_le hle with h | h
    · linarith
    · exact absurd h hne
  have hadm : (shiftMech m i0 c).Admissible := by
    refine ⟨shift_wd m hwd i0 c, ?_, ?_⟩
    · intro j x hx x' hx'
      rw [shift_Q, shift_T m hwd i0 c j hx, shift_T m hwd i0 c j hx']
      have := hIC j x hx x' hx'
      linarith
    · intro j x hx
      unfold DirectMechanism.interimU
      rw [shift_Q, shift_T m hwd i0 c j hx]
      have hU := interimU_mono m hIC j hlo hx hx.1
      have h0 := hIR j x hx
      unfold DirectMechanism.interimU at hU h0
      split_ifs with hj
      · subst hj; linarith
      · linarith
  have := hopt _ hadm
  rw [shift_rev m hwd] at this
  linarith


lemma f_ii (E : Environment ι) (i : ι) {a b : ℝ} (ha : a ∈ Set.Icc E.lo E.hi)
    (hb : b ∈ Set.Icc E.lo E.hi) : IntervalIntegrable (E.f i) volume a b :=
  (E.f_intervalIntegrable i).mono_set (by
    rw [Set.uIcc_of_le E.lo_lt_hi.le]; exact Set.uIcc_subset_Icc ha hb)

lemma one_sub_cdf (E : Environment ι) (i : ι) {y : ℝ} (hy : y ∈ Set.Icc E.lo E.hi) :
    ∫ x in y..E.hi, E.f i x = 1 - E.cdf i y := by
  have hlo : E.lo ∈ Set.Icc E.lo E.hi := ⟨le_rfl, E.lo_lt_hi.le⟩
  have hhi : E.hi ∈ Set.Icc E.lo E.hi := ⟨E.lo_lt_hi.le, le_rfl⟩
  rw [Environment.cdf, ← E.f_integral i,
    intervalIntegral.integral_interval_sub_left (f_ii E i hlo hhi) (f_ii E i hlo hy)]

lemma fubini_tri (E : Environment ι) (i : ι) (g : ℝ → ℝ) (hg : Measurable g)
    (hb : ∀ y, |g y| ≤ 1) :
    ∫ x in E.lo..E.hi, (∫ y in E.lo..x, g y) * E.f i x
      = ∫ y in E.lo..E.hi, g y * (1 - E.cdf i y) := by
  set S := Set.Icc E.lo E.hi with hS
  have hfS : Integrable (E.f i) (volume.restrict S) := f_integrableOn E i
  let k : ℝ → ℝ → ℝ := fun x y => (if y ≤ x then g y else 0) * E.f i x
  have hkm : Measurable (Function.uncurry k) := by
    apply Measurable.mul
    · exact Measurable.ite (measurableSet_le measurable_snd measurable_fst)
        (hg.comp measurable_snd) measurable_const
    · exact (E.f_measurable i).comp measurable_fst
  have hk : Integrable (Function.uncurry k) ((volume.restrict S).prod (volume.restrict S)) := by
    have hb' : Integrable (fun p : ℝ × ℝ => E.f i p.1 * 1)
        ((volume.restrict S).prod (volume.restrict S)) :=
      hfS.mul_prod (integrable_const 1)
    refine hb'.norm.mono' hkm.aestronglyMeasurable (Filter.Eventually.of_forall ?_)
    intro p
    simp only [Function.uncurry, k, norm_mul, mul_one, Real.norm_eq_abs, abs_abs]
    have : |(if p.2 ≤ p.1 then g p.2 else 0)| ≤ 1 := by
      split_ifs
      · exact hb _
      · simp
    exact mul_le_of_le_one_left (abs_nonneg _) this
  have hL : ∀ x ∈ S, ∫ y in S, k x y = (∫ y in E.lo..x, g y) * E.f i x := by
    intro x hx
    simp only [k]
    rw [integral_mul_const]
    congr 1
    have : (fun y => if y ≤ x then g y else 0) = (Set.Iic x).indicator g := by
      funext y; simp [Set.indicator_apply]
    rw [this, setIntegral_indicator measurableSet_Iic]
    have hset : S ∩ Set.Iic x = Set.Icc E.lo x := by
      ext y; simp only [hS, Set.mem_inter_iff, Set.mem_Icc, Set.mem_Iic]
      constructor
      · rintro ⟨⟨h1, _⟩, h3⟩; exact ⟨h1, h3⟩
      · rintro ⟨h1, h3⟩; exact ⟨⟨h1, le_trans h3 hx.2⟩, h3⟩
    rw [hset, integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hx.1]
  have hR : ∀ y ∈ S, ∫ x in S, k x y = g y * (1 - E.cdf i y) := by
    intro y hy
    simp only [k]
    have : (fun x => (if y ≤ x then g y else 0) * E.f i x)
        = (Set.Ici y).indicator (fun x => g y * E.f i x) := by
      funext x; simp [Set.indicator_apply]
    rw [this, setIntegral_indicator measurableSet_Ici, integral_const_mul]
    have hset : S ∩ Set.Ici y = Set.Icc y E.hi := by
      ext x; simp only [hS, Set.mem_inter_iff, Set.mem_Icc, Set.mem_Ici]
      constructor
      · rintro ⟨⟨_, h2⟩, h3⟩; exact ⟨h3, h2⟩
      · rintro ⟨h1, h3⟩; exact ⟨⟨le_trans hy.1 h1, h3⟩, h1⟩
    rw [hset, integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hy.2,
      one_sub_cdf E i hy]
  rw [intervalIntegral.integral_of_le E.lo_lt_hi.le, ← integral_Icc_eq_integral_Ioc,
    intervalIntegral.integral_of_le E.lo_lt_hi.le, ← integral_Icc_eq_integral_Ioc]
  rw [← setIntegral_congr_fun measurableSet_Icc hL, integral_integral_swap hk,
    setIntegral_congr_fun measurableSet_Icc hR]

lemma interimQ_abs_le (m : DirectMechanism E) (i : ι) {x : ℝ} (hx : x ∈ Set.Icc E.lo E.hi) :
    |m.interimQ i x| ≤ 1 := by
  have := norm_integral_le_of_norm_le_const (μ := E.prior) (C := 1)
    (f := fun θ => m.q i (Function.update θ i x)) (by
      filter_upwards [prior_ae_mem] with θ hθ
      have h0 := m.q_nonneg _ (update_mem hθ i hx) i
      have h1 := m.q_le_one _ (update_mem hθ i hx) i
      rw [Real.norm_eq_abs, abs_le]; constructor <;> linarith)
  simpa [DirectMechanism.interimQ] using this

lemma ext_abs_le (m : DirectMechanism E) (i : ι) (y : ℝ) :
    |ext (m.interimQ i) E.lo E.hi E.lo_lt_hi.le y| ≤ 1 :=
  interimQ_abs_le m i (Set.projIcc E.lo E.hi E.lo_lt_hi.le y).2

lemma bdd_f_ii (E : Environment ι) (i : ι) (h : ℝ → ℝ) (hm : Measurable h) (C : ℝ)
    (hC : ∀ y, |h y| ≤ C) : IntervalIntegrable (fun x => h x * E.f i x) volume E.lo E.hi := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le E.lo_lt_hi.le]
  have : IntegrableOn (E.f i) (Set.Ioc E.lo E.hi) :=
    (f_integrableOn E i).mono_set Set.Ioc_subset_Icc_self
  exact this.bdd_mul hm.aestronglyMeasurable (Filter.Eventually.of_forall (fun y => by
    rw [Real.norm_eq_abs]; exact hC y))

/-- general revenue formula for buyer `i` -/
lemma rev_i (m : DirectMechanism E) (hwd : m.WellDefined) (hIC : m.IsIC) (i : ι) :
    ∫ θ, m.t i θ ∂E.prior = (∫ x in E.lo..E.hi, m.interimQ i x * E.virtualValue i x * E.f i x)
      - (E.lo * m.interimQ i E.lo - m.interimT i E.lo) := by
  have hab := E.lo_lt_hi.le
  set Qe := ext (m.interimQ i) E.lo E.hi hab with hQe
  have hmono : Monotone Qe := ext_mono (isIC_abs m hIC i) hab
  have hQm : Measurable Qe := hmono.measurable
  have hQb : ∀ y, |Qe y| ≤ 1 := ext_abs_le m i
  have hQeq : ∀ x ∈ Set.Icc E.lo E.hi, m.interimQ i x = Qe x := fun x hx => (ext_eq hab hx).symm
  set c := E.lo * m.interimQ i E.lo - m.interimT i E.lo
  have hG : ∀ x ∈ Set.Icc E.lo E.hi, ∫ y in E.lo..x, m.interimQ i y = ∫ y in E.lo..x, Qe y := by
    intro x hx
    apply intervalIntegral.integral_congr
    intro y hy
    rw [Set.uIcc_of_le hx.1] at hy
    exact hQeq y ⟨hy.1, le_trans hy.2 hx.2⟩
  have hT : ∀ x ∈ Set.Icc E.lo E.hi,
      m.interimT i x = x * Qe x - (∫ y in E.lo..x, Qe y) - c := by
    intro x hx
    rw [revenue_equivalence_core m hIC i x hx, hG x hx, hQeq x hx]
    ring
  rw [integral_interim E i (hwd.t_integrable i)]
  have e1 : ∫ x, (∫ θ, m.t i (Function.update θ i x) ∂E.prior) ∂(E.marg i)
      = ∫ x, m.interimT i x ∂(E.marg i) := rfl
  rw [e1, integral_marg]
  have hU : Set.uIcc E.lo E.hi = Set.Icc E.lo E.hi := Set.uIcc_of_le hab
  -- rewrite integrands on [lo, hi]
  have e2 : ∫ x in E.lo..E.hi, m.interimT i x * E.f i x
      = ∫ x in E.lo..E.hi, (x * (Qe x * E.f i x) - (∫ y in E.lo..x, Qe y) * E.f i x
          - c * E.f i x) := by
    apply intervalIntegral.integral_congr
    intro x hx; rw [hU] at hx
    simp only; rw [hT x hx]; ring
  have e3 : ∫ x in E.lo..E.hi, m.interimQ i x * E.virtualValue i x * E.f i x
      = ∫ x in E.lo..E.hi, (x * (Qe x * E.f i x) - Qe x * (1 - E.cdf i x)) := by
    apply intervalIntegral.integral_congr
    intro x hx; rw [hU] at hx
    simp only; rw [hQeq x hx, Environment.virtualValue]
    have := (E.f_pos i x hx).ne'
    field_simp
  rw [e2, e3]
  have hQf : IntervalIntegrable (fun x => Qe x * E.f i x) volume E.lo E.hi :=
    bdd_f_ii E i Qe hQm 1 hQb
  have hxQf : IntervalIntegrable (fun x => x * (Qe x * E.f i x)) volume E.lo E.hi := by
    have := hQf.continuousOn_mul (g := fun x => x) continuousOn_id
    simpa using this
  have hGc : Continuous (fun x => ∫ y in E.lo..x, Qe y) :=
    intervalIntegral.continuous_primitive (fun a b => hmono.intervalIntegrable) E.lo
  have hGf : IntervalIntegrable (fun x => (∫ y in E.lo..x, Qe y) * E.f i x) volume E.lo E.hi := by
    have := (E.f_intervalIntegrable i).continuousOn_mul (g := fun x => ∫ y in E.lo..x, Qe y)
      hGc.continuousOn
    simpa [mul_comm] using this
  have hFc : ContinuousOn (fun x => 1 - E.cdf i x) (Set.uIcc E.lo E.hi) := by
    have := intervalIntegral.continuousOn_primitive_interval (μ := volume) (a := E.lo) (b := E.hi)
      (f := E.f i) (by rw [hU]; exact f_integrableOn E i)
    exact continuousOn_const.sub this
  have hQF : IntervalIntegrable (fun x => Qe x * (1 - E.cdf i x)) volume E.lo E.hi :=
    (hmono.intervalIntegrable).mul_continuousOn hFc
  have hcf : IntervalIntegrable (fun x => c * E.f i x) volume E.lo E.hi :=
    (E.f_intervalIntegrable i).const_mul c
  rw [intervalIntegral.integral_sub (hxQf.sub hGf) hcf,
    intervalIntegral.integral_sub hxQf hGf, intervalIntegral.integral_sub hxQf hQF,
    fubini_tri E i Qe hQm hQb, intervalIntegral.integral_const_mul, E.f_integral i]
  ring


lemma cdf_contOn (E : Environment ι) (i : ι) :
    ContinuousOn (E.cdf i) (Set.Icc E.lo E.hi) := by
  have := intervalIntegral.continuousOn_primitive_interval (μ := volume) (a := E.lo) (b := E.hi)
    (f := E.f i) (by rw [Set.uIcc_of_le E.lo_lt_hi.le]; exact f_integrableOn E i)
  rw [Set.uIcc_of_le E.lo_lt_hi.le] at this
  exact this

/-- clamped virtual value (measurable on all of ℝ) -/
noncomputable def vvC (E : Environment ι) (i : ι) (x : ℝ) : ℝ :=
  E.virtualValue i (Set.projIcc E.lo E.hi E.lo_lt_hi.le x)

lemma vvC_eq (E : Environment ι) (i : ι) {x : ℝ} (hx : x ∈ Set.Icc E.lo E.hi) :
    vvC E i x = E.virtualValue i x := by
  simp [vvC, Set.projIcc_of_mem _ hx]

lemma vvC_meas (E : Environment ι) (i : ι) : Measurable (vvC E i) := by
  have hp : Continuous (fun x => (Set.projIcc E.lo E.hi E.lo_lt_hi.le x : ℝ)) :=
    continuous_subtype_val.comp continuous_projIcc
  have hc : Continuous (fun x => E.cdf i (Set.projIcc E.lo E.hi E.lo_lt_hi.le x)) :=
    (cdf_contOn E i).comp_continuous hp (fun x => (Set.projIcc _ _ _ x).2)
  unfold vvC Environment.virtualValue
  exact hp.measurable.sub ((measurable_const.sub hc.measurable).div
    ((E.f_measurable i).comp hp.measurable))

lemma vvC_int (E : Environment ι) (i : ι) : Integrable (vvC E i) (E.marg i) := by
  have hab := E.lo_lt_hi.le
  rw [Environment.marg, integrable_withDensity_iff (E.f_measurable i).ennreal_ofReal
    (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  have hFc : ContinuousOn (fun x => 1 - E.cdf i x) (Set.uIcc E.lo E.hi) := by
    rw [Set.uIcc_of_le hab]; exact continuousOn_const.sub (cdf_contOn E i)
  have hI : IntervalIntegrable (fun x => x * E.f i x - (1 - E.cdf i x)) volume E.lo E.hi := by
    have h1 := (E.f_intervalIntegrable i).continuousOn_mul (g := fun x => x) continuousOn_id
    exact (by simpa [mul_comm] using h1 : IntervalIntegrable (fun x => x * E.f i x) volume E.lo E.hi).sub
      hFc.intervalIntegrable
  have hI' := (intervalIntegrable_iff_integrableOn_Icc_of_le hab).1 hI
  refine hI'.congr ?_
  filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
  rw [vvC_eq E i hx, ENNReal.toReal_ofReal (E.f_pos i x hx).le, Environment.virtualValue]
  have := (E.f_pos i x hx).ne'
  field_simp

lemma vs_i (m : DirectMechanism E) (hwd : m.WellDefined) (i : ι) :
    ∫ θ, m.q i θ * E.virtualValue i (θ i) ∂E.prior
      = ∫ x in E.lo..E.hi, m.interimQ i x * E.virtualValue i x * E.f i x := by
  have hae : ∀ᵐ θ ∂E.prior, m.q i θ * E.virtualValue i (θ i) = m.q i θ * vvC E i (θ i) := by
    filter_upwards [prior_ae_mem] with θ hθ
    rw [vvC_eq E i (hθ i trivial)]
  have hψint : Integrable (fun θ : ι → ℝ => vvC E i (θ i)) E.prior := by
    rw [prior_eq_pi]
    exact ((measurePreserving_eval (fun j => E.marg j) i).integrable_comp
      (vvC_meas E i).aestronglyMeasurable).2 (vvC_int E i)
  have hgi : Integrable (fun θ => m.q i θ * E.virtualValue i (θ i)) E.prior := by
    refine Integrable.congr ?_ (Filter.EventuallyEq.symm hae)
    refine hψint.norm.mono' (((hwd.q_measurable i).mul
      ((vvC_meas E i).comp (measurable_pi_apply i))).aestronglyMeasurable) ?_
    filter_upwards [prior_ae_mem] with θ hθ
    have h0 := m.q_nonneg θ hθ i
    have h1 := m.q_le_one θ hθ i
    rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg h0]
    exact mul_le_of_le_one_left (norm_nonneg _) h1
  rw [integral_interim E i hgi]
  simp only [Function.update_self, integral_mul_const]
  rw [integral_marg]
  rfl

theorem revenue_eq_virtual_surplus_core (m : DirectMechanism E) (hwd : m.WellDefined) (hIC : m.IsIC)
    (hlow : ∀ i, m.interimT i E.lo = E.lo * m.interimQ i E.lo) :
    m.revenue = ∑ i, ∫ x in E.lo..E.hi, m.interimQ i x * E.virtualValue i x * E.f i x ∧
    m.revenue = ∑ i, ∫ θ, m.q i θ * E.virtualValue i (θ i) ∂E.prior := by
  have h1 : m.revenue = ∑ i, ∫ x in E.lo..E.hi, m.interimQ i x * E.virtualValue i x * E.f i x := by
    unfold DirectMechanism.revenue
    apply Finset.sum_congr rfl
    intro i _
    rw [rev_i m hwd hIC i, hlow i]; ring
  refine ⟨h1, ?_⟩
  rw [h1]
  exact Finset.sum_congr rfl (fun i _ => (vs_i m hwd i).symm)

end MechanismDesign.Auctions

open MechanismDesign.Auctions


theorem solution {ι : Type*} [Fintype ι] [DecidableEq ι] {E : Environment ι}
    (m : DirectMechanism E) (hwd : m.WellDefined) (hIC : m.IsIC)
    (hlow : ∀ i, m.interimT i E.lo = E.lo * m.interimQ i E.lo) :
    m.revenue = ∑ i, ∫ x in E.lo..E.hi, m.interimQ i x * E.virtualValue i x * E.f i x ∧
    m.revenue = ∑ i, ∫ θ, m.q i θ * E.virtualValue i (θ i) ∂E.prior := by
  exact revenue_eq_virtual_surplus_core m hwd hIC hlow
