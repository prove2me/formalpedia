-- Prove2me | solution 1 for MechanismDesign.Auctions.myerson_optimal_auction
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T09:44:54.972671+00:00
-- url     : https://prove2.me/submissions/82ce1889-b1af-4398-a768-38f360b4f72c

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


lemma meas_upd (i : ι) (x : ℝ) : Measurable (fun θ : ι → ℝ => Function.update θ i x) :=
  measurable_update'.comp (measurable_id.prodMk measurable_const)

structure GoodAlloc (a : ι → (ι → ℝ) → ℝ) : Prop where
  meas : ∀ i, Measurable (a i)
  nonneg : ∀ i θ, 0 ≤ a i θ
  le_one : ∀ i θ, a i θ ≤ 1
  sum_le : ∀ θ, ∑ i, a i θ ≤ 1
  mono : ∀ i θ, Monotone (fun x => a i (Function.update θ i x))

noncomputable def QA (E : Environment ι) (a : ι → (ι → ℝ) → ℝ) (i : ι) (x : ℝ) : ℝ :=
  ∫ θ, a i (Function.update θ i x) ∂E.prior

noncomputable def tauA (E : Environment ι) (a : ι → (ι → ℝ) → ℝ) (i : ι) (x : ℝ) : ℝ :=
  (Set.projIcc E.lo E.hi E.lo_lt_hi.le x : ℝ) * QA E a i (Set.projIcc E.lo E.hi E.lo_lt_hi.le x : ℝ)
    - ∫ z in E.lo..(Set.projIcc E.lo E.hi E.lo_lt_hi.le x : ℝ), QA E a i z

noncomputable def mechA (E : Environment ι) (a : ι → (ι → ℝ) → ℝ) (ha : GoodAlloc a) :
    DirectMechanism E where
  q := a
  t := fun i θ => tauA E a i (θ i)
  q_nonneg := fun θ _ i => ha.nonneg i θ
  q_le_one := fun θ _ i => ha.le_one i θ
  sum_q_le_one := fun θ _ => ha.sum_le θ

section GA
variable {a : ι → (ι → ℝ) → ℝ} (ha : GoodAlloc a)
include ha

lemma upd_int (i : ι) (x : ℝ) : Integrable (fun θ => a i (Function.update θ i x)) E.prior :=
  (integrable_const (1 : ℝ)).mono' ((ha.meas i).comp (meas_upd i x)).aestronglyMeasurable
    (Filter.Eventually.of_forall (fun θ => by
      rw [Real.norm_eq_abs, abs_of_nonneg (ha.nonneg _ _)]; exact ha.le_one _ _))

lemma QA_mono (i : ι) : Monotone (QA E a i) := by
  intro x y hxy
  exact integral_mono (upd_int (E := E) ha i x) (upd_int ha i y) (fun θ => ha.mono i θ hxy)

lemma QA_abs (i : ι) (x : ℝ) : |QA E a i x| ≤ 1 := by
  have := norm_integral_le_of_norm_le_const (μ := E.prior) (C := 1)
    (f := fun θ => a i (Function.update θ i x)) (Filter.Eventually.of_forall (fun θ => by
      rw [Real.norm_eq_abs, abs_of_nonneg (ha.nonneg _ _)]; exact ha.le_one _ _))
  simpa [QA] using this

lemma tauA_meas (i : ι) : Measurable (tauA E a i) := by
  have hp : Continuous (fun x => (Set.projIcc E.lo E.hi E.lo_lt_hi.le x : ℝ)) :=
    continuous_subtype_val.comp continuous_projIcc
  have hQ : Measurable (QA E a i) := (QA_mono ha i).measurable
  have hG : Continuous (fun y => ∫ z in E.lo..y, QA E a i z) :=
    intervalIntegral.continuous_primitive (fun _ _ => (QA_mono ha i).intervalIntegrable) E.lo
  unfold tauA
  exact (hp.measurable.mul (hQ.comp hp.measurable)).sub (hG.comp hp).measurable

lemma tauA_bound (i : ι) (x : ℝ) : |tauA E a i x| ≤ 2 * E.hi := by
  set y : ℝ := (Set.projIcc E.lo E.hi E.lo_lt_hi.le x : ℝ)
  have hy : y ∈ Set.Icc E.lo E.hi := (Set.projIcc E.lo E.hi E.lo_lt_hi.le x).2
  have h0 := E.lo_nonneg
  have h1 : |y * QA E a i y| ≤ E.hi := by
    rw [abs_mul, abs_of_nonneg (by linarith [hy.1])]
    have := QA_abs (E := E) ha i y
    nlinarith [hy.2, hy.1]
  have h2 : ‖∫ z in E.lo..y, QA E a i z‖ ≤ 1 * |y - E.lo| :=
    intervalIntegral.norm_integral_le_of_norm_le_const (fun z _ => by
      rw [Real.norm_eq_abs]; exact QA_abs ha i z)
  rw [Real.norm_eq_abs, abs_of_nonneg (by linarith [hy.1] : 0 ≤ y - E.lo)] at h2
  unfold tauA
  calc |y * QA E a i y - ∫ z in E.lo..y, QA E a i z|
      ≤ |y * QA E a i y| + |∫ z in E.lo..y, QA E a i z| := _root_.abs_sub _ _
    _ ≤ 2 * E.hi := by linarith [hy.2]

lemma mechA_t (i : ι) (θ : ι → ℝ) : (mechA E a ha).t i θ = tauA E a i (θ i) := rfl

lemma mechA_Q : (mechA E a ha).interimQ = QA E a := rfl

lemma mechA_T (i : ι) (x : ℝ) : (mechA E a ha).interimT i x = tauA E a i x := by
  unfold DirectMechanism.interimT
  simp [mechA]

lemma tauA_eq (i : ι) {x : ℝ} (hx : x ∈ Set.Icc E.lo E.hi) :
    tauA E a i x = x * QA E a i x - ∫ z in E.lo..x, QA E a i z := by
  simp [tauA, Set.projIcc_of_mem _ hx]

lemma mechA_adm : (mechA E a ha).Admissible ∧
    ∀ i, ∀ x ∈ Set.Icc E.lo E.hi, (mechA E a ha).interimT i x
      = x * (mechA E a ha).interimQ i x - ∫ y in E.lo..x, (mechA E a ha).interimQ i y := by
  have hlo : E.lo ∈ Set.Icc E.lo E.hi := ⟨le_rfl, E.lo_lt_hi.le⟩
  have hT : ∀ i, ∀ x ∈ Set.Icc E.lo E.hi, (mechA E a ha).interimT i x
      = x * (mechA E a ha).interimQ i x - ∫ y in E.lo..x, (mechA E a ha).interimQ i y := by
    intro i x hx; rw [mechA_T, mechA_Q, tauA_eq ha i hx]
  have hint : ∀ i, Integrable (fun θ : ι → ℝ => tauA E a i (θ i)) E.prior := by
    intro i
    exact (integrable_const (2 * E.hi)).mono'
      ((tauA_meas ha i).comp (measurable_pi_apply i)).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun θ => by rw [Real.norm_eq_abs]; exact tauA_bound ha i _))
  have hwd : (mechA E a ha).WellDefined := by
    refine ⟨ha.meas, fun i => (tauA_meas ha i).comp (measurable_pi_apply i), hint, ?_⟩
    intro i x _
    have : (fun θ => (mechA E a ha).t i (Function.update θ i x)) = fun _ => tauA E a i x := by
      funext θ; rw [mechA_t, Function.update_self]
    rw [this]
    exact integrable_const _
  have hIC : (mechA E a ha).IsIC := by
    rw [ic_iff_core]
    intro i
    refine ⟨(QA_mono ha i).monotoneOn _, ?_⟩
    intro x hx
    rw [hT i x hx, hT i E.lo hlo]
    simp
  refine ⟨⟨hwd, hIC, ?_⟩, hT⟩
  rw [ir_iff_core _ hIC]
  intro i
  rw [hT i E.lo hlo]
  simp

end GA


open Classical in
lemma pw {κ : Type*} [Fintype κ] [Nonempty κ] (v q : κ → ℝ) (hq0 : ∀ i, 0 ≤ q i)
    (hqs : ∑ i, q i ≤ 1) (hties : ∀ i j, i ≠ j → v i ≠ v j) (hnz : ∀ i, v i ≠ 0) (a : κ → ℝ)
    (ha : ∀ i, a i = if 0 < v i ∧ ∀ j, j ≠ i → v j < v i then 1 else 0) :
    ∑ i, q i * v i ≤ ∑ i, a i * v i ∧ (∑ i, a i * v i ≤ ∑ i, q i * v i → ∀ i, q i = a i) := by
  classical
  obtain ⟨w, -, hw⟩ := Finset.exists_max_image Finset.univ v Finset.univ_nonempty
  have hlt : ∀ j, j ≠ w → v j < v w :=
    fun j hj => lt_of_le_of_ne (hw j (Finset.mem_univ _)) (hties j w hj)
  by_cases hpos : 0 < v w
  · have haw : a w = 1 := by rw [ha, if_pos ⟨hpos, hlt⟩]
    have haj : ∀ j, j ≠ w → a j = 0 := by
      intro j hj; rw [ha, if_neg]; rintro ⟨_, h⟩
      exact absurd (h w (Ne.symm hj)) (not_lt.2 (le_of_lt (hlt j hj)))
    have hsa : ∑ i, a i * v i = v w := by
      rw [Finset.sum_eq_single w (fun j _ hj => by rw [haj j hj, zero_mul]) (by simp), haw, one_mul]
    rw [hsa]
    have e : ∑ i, q i * (v w - v i) = (∑ i, q i) * v w - ∑ i, q i * v i := by
      rw [Finset.sum_mul, ← Finset.sum_sub_distrib]; congr 1; funext i; ring
    have hn : ∀ i ∈ Finset.univ, 0 ≤ q i * (v w - v i) :=
      fun i _ => mul_nonneg (hq0 i) (by linarith [hw i (Finset.mem_univ _)])
    have hs0 : 0 ≤ ∑ i, q i * (v w - v i) := Finset.sum_nonneg hn
    have hr : 0 ≤ v w * (1 - ∑ i, q i) := mul_nonneg hpos.le (by linarith)
    refine ⟨by nlinarith, ?_⟩
    intro hle
    have hz : ∑ i, q i * (v w - v i) = 0 := by nlinarith
    have hz2 : v w * (1 - ∑ i, q i) = 0 := by nlinarith
    have hzi := (Finset.sum_eq_zero_iff_of_nonneg hn).1 hz
    have hqj : ∀ j, j ≠ w → q j = 0 := by
      intro j hj
      have := hzi j (Finset.mem_univ _)
      rcases mul_eq_zero.1 this with h | h
      · exact h
      · linarith [hlt j hj]
    have hsum1 : ∑ i, q i = 1 := by
      rcases mul_eq_zero.1 hz2 with h | h
      · linarith
      · linarith
    have hqw : q w = 1 := by
      rw [Finset.sum_eq_single w (fun j _ hj => hqj j hj) (by simp)] at hsum1
      exact hsum1
    intro i
    rcases eq_or_ne i w with rfl | hi
    · rw [hqw, haw]
    · rw [hqj i hi, haj i hi]
  · have hneg : ∀ i, v i < 0 := fun i =>
      lt_of_le_of_ne (le_trans (hw i (Finset.mem_univ _)) (not_lt.1 hpos)) (hnz i)
    have ha0 : ∀ i, a i = 0 := fun i => by
      rw [ha, if_neg]; rintro ⟨h, _⟩; linarith [hneg i]
    simp only [ha0, zero_mul, Finset.sum_const_zero]
    have hn : ∀ i ∈ Finset.univ, q i * v i ≤ 0 :=
      fun i _ => mul_nonpos_of_nonneg_of_nonpos (hq0 i) (hneg i).le
    refine ⟨Finset.sum_nonpos hn, ?_⟩
    intro hle i
    have hz : ∑ i, q i * v i = 0 := le_antisymm (Finset.sum_nonpos hn) hle
    have := (Finset.sum_eq_zero_iff_of_nonpos hn).1 hz i (Finset.mem_univ _)
    rcases mul_eq_zero.1 this with h | h
    · exact h
    · exact absurd h (hnz i)

lemma marg_null (E : Environment ι) (i : ι) {S : Set ℝ} (hS : MeasurableSet S)
    (h : (S ∩ Set.Icc E.lo E.hi).Subsingleton) : E.marg i S = 0 := by
  rw [marg_apply E i hS]
  have : volume (S ∩ Set.Icc E.lo E.hi) = 0 := h.measure_zero volume
  rw [Measure.restrict_eq_zero.2 this, lintegral_zero_measure]

lemma prior_null (E : Environment ι) (i : ι) {A : Set (ι → ℝ)} (hA : MeasurableSet A)
    (h : ∀ θ, E.marg i {x | Function.update θ i x ∈ A} = 0) : E.prior A = 0 := by
  have mp := update_mp E i
  rw [← mp.measure_preimage hA.nullMeasurableSet, Measure.prod_apply (mp.measurable hA)]
  have : ∀ θ, E.marg i (Prod.mk θ ⁻¹' ((fun p : (ι → ℝ) × ℝ => Function.update p.1 i p.2) ⁻¹' A))
      = 0 := h
  simp_rw [this]
  exact lintegral_zero

lemma ae_good (E : Environment ι) (φ : ι → ℝ → ℝ) (hm : ∀ i, Measurable (φ i))
    (hs : ∀ i, StrictMonoOn (φ i) (Set.Icc E.lo E.hi)) :
    ∀ᵐ θ ∂E.prior, θ ∈ E.typeSpace ∧ (∀ i j, i ≠ j → φ i (θ i) ≠ φ j (θ j)) ∧
      ∀ i, φ i (θ i) ≠ 0 := by
  have h1 : ∀ i j, ∀ᵐ θ ∂E.prior, i ≠ j → φ i (θ i) ≠ φ j (θ j) := by
    intro i j
    by_cases hij : i = j
    · exact Filter.Eventually.of_forall (fun θ h => absurd hij h)
    have hA : MeasurableSet {θ : ι → ℝ | φ i (θ i) = φ j (θ j)} :=
      measurableSet_eq_fun ((hm i).comp (measurable_pi_apply i)) ((hm j).comp (measurable_pi_apply j))
    have h0 : E.prior {θ : ι → ℝ | φ i (θ i) = φ j (θ j)} = 0 := by
      apply prior_null E i hA
      intro θ
      have hset : {x | Function.update θ i x ∈ {θ : ι → ℝ | φ i (θ i) = φ j (θ j)}}
          = {x | φ i x = φ j (θ j)} := by
        ext x; simp [Function.update_of_ne (Ne.symm hij)]
      rw [hset]
      apply marg_null E i (measurableSet_eq_fun (hm i) measurable_const)
      intro x hx y hy
      exact (hs i).injOn hx.2 hy.2 (by rw [hx.1, hy.1])
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 h0] with θ hθ _ heq
    exact hθ heq
  have h2 : ∀ i, ∀ᵐ θ ∂E.prior, φ i (θ i) ≠ 0 := by
    intro i
    have hA : MeasurableSet {θ : ι → ℝ | φ i (θ i) = 0} :=
      measurableSet_eq_fun ((hm i).comp (measurable_pi_apply i)) measurable_const
    have h0 : E.prior {θ : ι → ℝ | φ i (θ i) = 0} = 0 := by
      apply prior_null E i hA
      intro θ
      have hset : {x | Function.update θ i x ∈ {θ : ι → ℝ | φ i (θ i) = 0}} = {x | φ i x = 0} := by
        ext x; simp
      rw [hset]
      apply marg_null E i (measurableSet_eq_fun (hm i) measurable_const)
      intro x hx y hy
      exact (hs i).injOn hx.2 hy.2 (by rw [hx.1, hy.1])
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 h0] with θ hθ heq
    exact hθ heq
  have h1' : ∀ᵐ θ ∂E.prior, ∀ i j, i ≠ j → φ i (θ i) ≠ φ j (θ j) :=
    ae_all_iff.2 (fun i => ae_all_iff.2 (fun j => h1 i j))
  have h2' : ∀ᵐ θ ∂E.prior, ∀ i, φ i (θ i) ≠ 0 := ae_all_iff.2 h2
  filter_upwards [prior_ae_mem, h1', h2'] with θ a b c
  exact ⟨a, b, c⟩

/-- generic arg-max allocation rule with reserve `c` -/
noncomputable def amax (φ : ι → ℝ → ℝ) (c : ℝ) (i : ι) (θ : ι → ℝ) : ℝ := by
  classical
  exact if c < φ i (θ i) ∧ ∀ j, j ≠ i → φ j (θ j) < φ i (θ i) then 1 else 0

lemma amax_good (φ : ι → ℝ → ℝ) (c : ℝ) (hm : ∀ i, Measurable (φ i)) (hmono : ∀ i, Monotone (φ i)) :
    GoodAlloc (amax φ c) := by
  classical
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro i
    unfold amax
    apply Measurable.ite _ measurable_const measurable_const
    have e : {θ : ι → ℝ | c < φ i (θ i) ∧ ∀ j, j ≠ i → φ j (θ j) < φ i (θ i)}
        = {θ | c < φ i (θ i)} ∩ ⋂ j, {θ | j ≠ i → φ j (θ j) < φ i (θ i)} := by
      ext θ; simp
    rw [e]
    refine (measurableSet_lt measurable_const ((hm i).comp (measurable_pi_apply i))).inter
      (MeasurableSet.iInter fun j => ?_)
    by_cases hj : j = i
    · have : {θ : ι → ℝ | j ≠ i → φ j (θ j) < φ i (θ i)} = Set.univ := by
        ext θ; simp [hj]
      rw [this]; exact MeasurableSet.univ
    · have : {θ : ι → ℝ | j ≠ i → φ j (θ j) < φ i (θ i)} = {θ | φ j (θ j) < φ i (θ i)} := by
        ext θ; simp [hj]
      rw [this]
      exact measurableSet_lt ((hm j).comp (measurable_pi_apply j)) ((hm i).comp (measurable_pi_apply i))
  · intro i θ; unfold amax; split_ifs <;> norm_num
  · intro i θ; unfold amax; split_ifs <;> norm_num
  · intro θ
    by_cases h : ∃ i, c < φ i (θ i) ∧ ∀ j, j ≠ i → φ j (θ j) < φ i (θ i)
    · obtain ⟨w, hw⟩ := h
      rw [Finset.sum_eq_single w]
      · unfold amax; split_ifs <;> norm_num
      · intro j _ hj
        unfold amax
        rw [if_neg]
        rintro ⟨_, h2⟩
        exact absurd (h2 w (Ne.symm hj)) (not_lt.2 (le_of_lt (hw.2 j hj)))
      · simp
    · push_neg at h
      rw [Finset.sum_eq_zero]
      · norm_num
      · intro i _
        unfold amax
        rw [if_neg]
        rintro ⟨h1, h2⟩
        obtain ⟨j, hj, hj'⟩ := h i h1
        exact absurd (h2 j hj) (not_lt.2 hj')
  · intro i θ x y hxy
    unfold amax
    simp only [Function.update_self]
    have hφ := hmono i hxy
    split_ifs with h1 h2 h2
    · exact le_rfl
    · exfalso; apply h2
      refine ⟨lt_of_lt_of_le h1.1 hφ, fun j hj => ?_⟩
      have := h1.2 j hj
      rw [Function.update_of_ne hj] at this ⊢
      exact lt_of_lt_of_le this hφ
    · norm_num
    · exact le_rfl

lemma pay_ineq (m : DirectMechanism E) (hm : m.Admissible) :
    ∀ i, ∀ x ∈ Set.Icc E.lo E.hi,
      m.interimT i x ≤ x * m.interimQ i x - ∫ y in E.lo..x, m.interimQ i y := by
  intro i x hx
  have h1 := revenue_equivalence_core m hm.2.1 i x hx
  have h2 := (ir_iff_core m hm.2.1).1 hm.2.2 i
  linarith

lemma sum_int (m : DirectMechanism E) (hwd : m.WellDefined) (φ : ι → ℝ → ℝ) (hφ : ∀ i, Measurable (φ i))
    (hφi : ∀ i, Integrable (fun θ : ι → ℝ => φ i (θ i)) E.prior) :
    Integrable (fun θ => ∑ i, m.q i θ * φ i (θ i)) E.prior := by
  refine integrable_finset_sum _ (fun i _ => ?_)
  refine (hφi i).norm.mono' (((hwd.q_measurable i).mul
    ((hφ i).comp (measurable_pi_apply i))).aestronglyMeasurable) ?_
  filter_upwards [prior_ae_mem] with θ hθ
  have h0 := m.q_nonneg θ hθ i
  have h1 := m.q_le_one θ hθ i
  rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg h0]
  exact mul_le_of_le_one_left (norm_nonneg _) h1


lemma ae_eq_of_int_eq {f g : (ι → ℝ) → ℝ} (hf : Integrable f E.prior) (hg : Integrable g E.prior)
    (hle : ∀ᵐ θ ∂E.prior, f θ ≤ g θ) (heq : ∫ θ, f θ ∂E.prior = ∫ θ, g θ ∂E.prior) :
    ∀ᵐ θ ∂E.prior, g θ ≤ f θ := by
  have h0 : ∀ᵐ θ ∂E.prior, 0 ≤ (g - f) θ := hle.mono fun θ h => by simp only [Pi.sub_apply]; linarith
  have := (integral_eq_zero_iff_of_nonneg_ae h0 (hg.sub hf)).1 (by
    simp only [Pi.sub_apply]; rw [integral_sub hg hf, heq, sub_self])
  filter_upwards [this] with θ h
  simp only [Pi.sub_apply, Pi.zero_apply] at h
  linarith

lemma coord_int (E : Environment ι) (i : ι) : Integrable (fun θ : ι → ℝ => θ i) E.prior :=
  (integrable_const E.hi).mono' (measurable_pi_apply i).aestronglyMeasurable (by
    filter_upwards [prior_ae_mem] with θ hθ
    have := hθ i trivial
    rw [Real.norm_eq_abs, abs_of_nonneg (le_trans E.lo_nonneg this.1)]
    exact this.2)

noncomputable def effA : ι → (ι → ℝ) → ℝ := amax (fun _ => id) (-1)

lemma effA_good : GoodAlloc (effA (ι := ι)) :=
  amax_good _ _ (fun _ => measurable_id) (fun _ => monotone_id)

lemma effA_eq {θ : ι → ℝ} (hθ : θ ∈ E.typeSpace) (i : ι) : effA i θ = efficientAlloc i θ := by
  have hpos : (-1 : ℝ) < θ i := by linarith [(hθ i trivial).1, E.lo_nonneg]
  unfold effA amax efficientAlloc
  simp only [id, hpos, true_and]

theorem welfare_maximization_core (E : Environment ι) :
    (∃ m : DirectMechanism E, m.Admissible ∧
      (∀ i, ∀ θ ∈ E.typeSpace, m.q i θ = efficientAlloc i θ) ∧
      ∀ i, ∀ x ∈ Set.Icc E.lo E.hi,
        m.interimT i x ≤ x * m.interimQ i x - ∫ y in E.lo..x, m.interimQ i y) ∧
    ∀ m : DirectMechanism E, m.Admissible →
      ((∀ m' : DirectMechanism E, m'.Admissible → m'.welfare ≤ m.welfare) ↔
        ((∀ i, ∀ᵐ θ ∂E.prior, m.q i θ = efficientAlloc i θ) ∧
          ∀ i, ∀ x ∈ Set.Icc E.lo E.hi,
            m.interimT i x ≤ x * m.interimQ i x - ∫ y in E.lo..x, m.interimQ i y)) := by
  classical
  have hne : Nonempty ι := by
    have := E.two_le_card
    exact Fintype.card_pos_iff.1 (by omega)
  set me := mechA E effA effA_good with hme
  obtain ⟨hadm, hT⟩ := mechA_adm (E := E) effA_good
  have hint : ∀ m : DirectMechanism E, m.WellDefined →
      Integrable (fun θ => ∑ i, m.q i θ * θ i) E.prior :=
    fun m hwd => sum_int m hwd (fun _ => id) (fun _ => measurable_id) (fun i => coord_int E i)
  have hgood := ae_good E (fun _ => id) (fun _ => measurable_id) (fun _ => strictMonoOn_id)
  -- pointwise comparison at good θ
  have hpw : ∀ m : DirectMechanism E, ∀ θ, (θ ∈ E.typeSpace ∧ (∀ i j, i ≠ j → θ i ≠ θ j) ∧
      ∀ i, θ i ≠ 0) →
      ∑ i, m.q i θ * θ i ≤ ∑ i, efficientAlloc i θ * θ i ∧
      (∑ i, efficientAlloc i θ * θ i ≤ ∑ i, m.q i θ * θ i → ∀ i, m.q i θ = efficientAlloc i θ) := by
    intro m θ ⟨hθ, ht, hz⟩
    have hpos : ∀ i, 0 < θ i := fun i =>
      lt_of_le_of_ne (le_trans E.lo_nonneg (hθ i trivial).1) (Ne.symm (hz i))
    apply pw (fun i => θ i) (fun i => m.q i θ) (fun i => m.q_nonneg θ hθ i) (m.sum_q_le_one θ hθ)
      ht hz
    intro i
    unfold efficientAlloc
    simp only [hpos i, true_and]
  have hsum_eff : ∀ θ ∈ E.typeSpace, ∑ i, me.q i θ * θ i = ∑ i, efficientAlloc i θ * θ i := by
    intro θ hθ
    exact Finset.sum_congr rfl (fun i _ => by rw [show me.q i θ = effA i θ from rfl, effA_eq hθ])
  have hW : me.welfare = ∫ θ, ∑ i, efficientAlloc i θ * θ i ∂E.prior := by
    unfold DirectMechanism.welfare
    apply integral_congr_ae
    filter_upwards [prior_ae_mem] with θ hθ
    exact hsum_eff θ hθ
  have hle : ∀ m' : DirectMechanism E, m'.Admissible → m'.welfare ≤ me.welfare := by
    intro m' hm'
    unfold DirectMechanism.welfare
    apply integral_mono_ae (hint m' hm'.1) (hint me hadm.1)
    filter_upwards [hgood] with θ hθ
    rw [hsum_eff θ hθ.1]
    exact (hpw m' θ hθ).1
  refine ⟨⟨me, hadm, fun i θ hθ => effA_eq hθ i, fun i x hx => le_of_eq (hT i x hx)⟩, ?_⟩
  intro m hm
  constructor
  · intro hopt
    refine ⟨?_, pay_ineq m hm⟩
    have h1 := hopt me hadm
    have h2 := hle m hm
    have hae := ae_eq_of_int_eq (hint m hm.1) (hint me hadm.1) (by
        filter_upwards [hgood] with θ hθ
        rw [hsum_eff θ hθ.1]; exact (hpw m θ hθ).1)
      (by unfold DirectMechanism.welfare at h1 h2; linarith)
    intro i
    filter_upwards [hae, hgood] with θ h hθ
    rw [hsum_eff θ hθ.1] at h
    exact (hpw m θ hθ).2 h i
  · rintro ⟨hq, -⟩ m' hm'
    have : m.welfare = me.welfare := by
      rw [hW]
      unfold DirectMechanism.welfare
      apply integral_congr_ae
      filter_upwards [ae_all_iff.2 hq] with θ h
      exact Finset.sum_congr rfl (fun i _ => by rw [h i])
    rw [this]; exact hle m' hm'


lemma vvC_prior_int (E : Environment ι) (i : ι) :
    Integrable (fun θ : ι → ℝ => vvC E i (θ i)) E.prior := by
  rw [prior_eq_pi]
  exact ((measurePreserving_eval (fun j => E.marg j) i).integrable_comp
    (vvC_meas E i).aestronglyMeasurable).2 (vvC_int E i)

lemma vvC_mono (hreg : E.Regular) (i : ι) : Monotone (vvC E i) := by
  intro x y hxy
  exact (hreg i).monotoneOn (Set.projIcc E.lo E.hi E.lo_lt_hi.le x).2
    (Set.projIcc E.lo E.hi E.lo_lt_hi.le y).2 (Set.monotone_projIcc E.lo_lt_hi.le hxy)

lemma vvC_smono (hreg : E.Regular) (i : ι) : StrictMonoOn (vvC E i) (Set.Icc E.lo E.hi) := by
  intro x hx y hy hxy
  rw [vvC_eq E i hx, vvC_eq E i hy]
  exact hreg i hx hy hxy

lemma rev_formula (m : DirectMechanism E) (hwd : m.WellDefined) (hIC : m.IsIC) :
    m.revenue = (∫ θ, ∑ i, m.q i θ * vvC E i (θ i) ∂E.prior)
      - ∑ i, (E.lo * m.interimQ i E.lo - m.interimT i E.lo) := by
  have hI : ∀ i, Integrable (fun θ => m.q i θ * vvC E i (θ i)) E.prior := by
    intro i
    refine (vvC_prior_int E i).norm.mono' (((hwd.q_measurable i).mul
      ((vvC_meas E i).comp (measurable_pi_apply i))).aestronglyMeasurable) ?_
    filter_upwards [prior_ae_mem] with θ hθ
    have h0 := m.q_nonneg θ hθ i
    have h1 := m.q_le_one θ hθ i
    rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg h0]
    exact mul_le_of_le_one_left (norm_nonneg _) h1
  rw [integral_finset_sum _ (fun i _ => hI i), ← Finset.sum_sub_distrib]
  unfold DirectMechanism.revenue
  apply Finset.sum_congr rfl
  intro i _
  rw [rev_i m hwd hIC i, ← vs_i m hwd i]
  congr 1
  apply integral_congr_ae
  filter_upwards [prior_ae_mem] with θ hθ
  rw [vvC_eq E i (hθ i trivial)]

noncomputable def myA (E : Environment ι) : ι → (ι → ℝ) → ℝ := amax (vvC E) 0

lemma myA_eq {θ : ι → ℝ} (hθ : θ ∈ E.typeSpace) (i : ι) : myA E i θ = E.myersonAlloc i θ := by
  have hv : ∀ j, vvC E j (θ j) = E.virtualValue j (θ j) := fun j => vvC_eq E j (hθ j trivial)
  unfold myA amax Environment.myersonAlloc
  simp only [hv]

theorem myerson_optimal_auction_core (E : Environment ι) (hreg : E.Regular) :
    (∃ m : DirectMechanism E, m.Admissible ∧
      (∀ i, ∀ θ ∈ E.typeSpace, m.q i θ = E.myersonAlloc i θ) ∧
      ∀ i, ∀ x ∈ Set.Icc E.lo E.hi,
        m.interimT i x = x * m.interimQ i x - ∫ y in E.lo..x, m.interimQ i y) ∧
    ∀ m : DirectMechanism E, m.Admissible →
      ((∀ m' : DirectMechanism E, m'.Admissible → m'.revenue ≤ m.revenue) ↔
        ((∀ i, ∀ᵐ θ ∂E.prior, m.q i θ = E.myersonAlloc i θ) ∧
          ∀ i, ∀ x ∈ Set.Icc E.lo E.hi,
            m.interimT i x = x * m.interimQ i x - ∫ y in E.lo..x, m.interimQ i y)) := by
  classical
  have hne : Nonempty ι := by
    have := E.two_le_card
    exact Fintype.card_pos_iff.1 (by omega)
  have hlo : E.lo ∈ Set.Icc E.lo E.hi := ⟨le_rfl, E.lo_lt_hi.le⟩
  have hga : GoodAlloc (myA E) := amax_good _ _ (vvC_meas E) (vvC_mono hreg)
  set ms := mechA E (myA E) hga with hms
  obtain ⟨hadm, hT⟩ := mechA_adm (E := E) hga
  have hint : ∀ m : DirectMechanism E, m.WellDefined →
      Integrable (fun θ => ∑ i, m.q i θ * vvC E i (θ i)) E.prior :=
    fun m hwd => sum_int m hwd (vvC E) (vvC_meas E) (fun i => vvC_prior_int E i)
  have hgood := ae_good E (vvC E) (vvC_meas E) (vvC_smono hreg)
  have hpw : ∀ m : DirectMechanism E, ∀ θ, (θ ∈ E.typeSpace ∧
      (∀ i j, i ≠ j → vvC E i (θ i) ≠ vvC E j (θ j)) ∧ ∀ i, vvC E i (θ i) ≠ 0) →
      ∑ i, m.q i θ * vvC E i (θ i) ≤ ∑ i, myA E i θ * vvC E i (θ i) ∧
      (∑ i, myA E i θ * vvC E i (θ i) ≤ ∑ i, m.q i θ * vvC E i (θ i) →
        ∀ i, m.q i θ = myA E i θ) := by
    intro m θ ⟨hθ, ht, hz⟩
    apply pw (fun i => vvC E i (θ i)) (fun i => m.q i θ) (fun i => m.q_nonneg θ hθ i)
      (m.sum_q_le_one θ hθ) ht hz
    intro i
    by_cases h : 0 < vvC E i (θ i) ∧ ∀ j, j ≠ i → vvC E j (θ j) < vvC E i (θ i)
    · rw [if_pos h]; simp only [myA, amax]; rw [if_pos h]
    · rw [if_neg h]; simp only [myA, amax]; rw [if_neg h]
  -- the constructed mechanism has no slack at the bottom
  have hc0 : ∀ i, E.lo * ms.interimQ i E.lo - ms.interimT i E.lo = 0 := by
    intro i; rw [hT i E.lo hlo, intervalIntegral.integral_same, sub_zero]; exact sub_self _
  have hRs : ms.revenue = ∫ θ, ∑ i, myA E i θ * vvC E i (θ i) ∂E.prior := by
    rw [rev_formula ms hadm.1 hadm.2.1]
    simp only [hc0, Finset.sum_const_zero, sub_zero]
    rfl
  have hcn : ∀ m : DirectMechanism E, m.Admissible →
      ∀ i, 0 ≤ E.lo * m.interimQ i E.lo - m.interimT i E.lo := by
    intro m hm i
    have := (ir_iff_core m hm.2.1).1 hm.2.2 i
    linarith
  have hRle : ∀ m : DirectMechanism E, m.Admissible →
      (∫ θ, ∑ i, m.q i θ * vvC E i (θ i) ∂E.prior)
        ≤ ∫ θ, ∑ i, myA E i θ * vvC E i (θ i) ∂E.prior := by
    intro m hm
    apply integral_mono_ae (hint m hm.1) (hint ms hadm.1)
    filter_upwards [hgood] with θ hθ
    exact (hpw m θ hθ).1
  have hle : ∀ m' : DirectMechanism E, m'.Admissible → m'.revenue ≤ ms.revenue := by
    intro m' hm'
    rw [rev_formula m' hm'.1 hm'.2.1, hRs]
    have := Finset.sum_nonneg (fun i (_ : i ∈ Finset.univ) => hcn m' hm' i)
    linarith [hRle m' hm']
  refine ⟨⟨ms, hadm, fun i θ hθ => myA_eq hθ i, hT⟩, ?_⟩
  intro m hm
  constructor
  · intro hopt
    have h1 := hopt ms hadm
    rw [rev_formula m hm.1 hm.2.1, hRs] at h1
    have hsn := Finset.sum_nonneg (fun i (_ : i ∈ Finset.univ) => hcn m hm i)
    have hR := hRle m hm
    have hsum0 : ∑ i, (E.lo * m.interimQ i E.lo - m.interimT i E.lo) = 0 := by linarith
    have hci := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hcn m hm i)).1 hsum0
    refine ⟨?_, ?_⟩
    · have hae := ae_eq_of_int_eq (hint m hm.1) (hint ms hadm.1) (by
          filter_upwards [hgood] with θ hθ
          exact (hpw m θ hθ).1)
        (by show _ = ∫ θ, ∑ i, myA E i θ * vvC E i (θ i) ∂E.prior; linarith)
      intro i
      filter_upwards [hae, hgood] with θ h hθ
      rw [(hpw m θ hθ).2 h i, myA_eq hθ.1 i]
    · intro i x hx
      have h := hci i (Finset.mem_univ _)
      rw [revenue_equivalence_core m hm.2.1 i x hx]
      linarith
  · rintro ⟨hq, hpay⟩ m' hm'
    have hc : ∀ i, E.lo * m.interimQ i E.lo - m.interimT i E.lo = 0 := by
      intro i; rw [hpay i E.lo hlo]; simp
    have : m.revenue = ms.revenue := by
      rw [rev_formula m hm.1 hm.2.1, hRs]
      simp only [hc, Finset.sum_const_zero, sub_zero]
      apply integral_congr_ae
      filter_upwards [ae_all_iff.2 hq, prior_ae_mem] with θ h hθ
      exact Finset.sum_congr rfl (fun i _ => by rw [h i, myA_eq hθ i])
    rw [this]; exact hle m' hm'

end MechanismDesign.Auctions

open MechanismDesign.Auctions


theorem solution {ι : Type*} [Fintype ι] [DecidableEq ι] (E : Environment ι)
    (hreg : E.Regular) :
    (∃ m : DirectMechanism E, m.Admissible ∧
      (∀ i, ∀ θ ∈ E.typeSpace, m.q i θ = E.myersonAlloc i θ) ∧
      ∀ i, ∀ x ∈ Set.Icc E.lo E.hi,
        m.interimT i x = x * m.interimQ i x - ∫ y in E.lo..x, m.interimQ i y) ∧
    ∀ m : DirectMechanism E, m.Admissible →
      ((∀ m' : DirectMechanism E, m'.Admissible → m'.revenue ≤ m.revenue) ↔
        ((∀ i, ∀ᵐ θ ∂E.prior, m.q i θ = E.myersonAlloc i θ) ∧
          ∀ i, ∀ x ∈ Set.Icc E.lo E.hi,
            m.interimT i x = x * m.interimQ i x - ∫ y in E.lo..x, m.interimQ i y)) := by
  exact myerson_optimal_auction_core E hreg
