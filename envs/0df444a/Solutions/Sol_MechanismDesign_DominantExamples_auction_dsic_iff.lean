-- Prove2me | solution 1 for MechanismDesign.DominantExamples.auction_dsic_iff
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T09:28:32.218219+00:00
-- url     : https://prove2.me/submissions/e519c91f-b485-45fa-934b-12ebb46eb9b2

import Mathlib
import Definitions.Def_MechanismDesign_DominantExamples_Auction

open MeasureTheory

namespace MechanismDesign.DominantExamples

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


lemma abs_of_formula {Q T : ℝ → ℝ} {a b : ℝ} (hm : MonotoneOn Q (Set.Icc a b))
    (hT : ∀ x ∈ Set.Icc a b, T x = T a + (x * Q x - a * Q a) - ∫ y in a..x, Q y)
    (hab : a ≤ b) : ICabs Q T a b := by
  intro x hx x' hx'
  have hint : ∀ u ∈ Set.Icc a b, ∀ v ∈ Set.Icc a b,
      IntervalIntegrable Q volume u v := by
    intro u hu v hv
    apply MonotoneOn.intervalIntegrable
    exact hm.mono (Set.uIcc_subset_Icc hu hv)
  have ha : a ∈ Set.Icc a b := ⟨le_rfl, hab⟩
  have eT := hT x hx
  have eT' := hT x' hx'
  have hsplit : (∫ y in a..x, Q y) - ∫ y in a..x', Q y = ∫ y in x'..x, Q y := by
    rw [intervalIntegral.integral_interval_sub_left (hint _ ha _ hx) (hint _ ha _ hx')]
  have key : (x - x') * Q x' ≤ ∫ y in x'..x, Q y := by
    rcases le_total x' x with hle | hle
    · have : ∫ y in x'..x, Q x' ≤ ∫ y in x'..x, Q y := by
        apply intervalIntegral.integral_mono_on hle intervalIntegrable_const (hint _ hx' _ hx)
        intro y hy
        exact hm hx' ⟨le_trans hx'.1 hy.1, le_trans hy.2 hx.2⟩ hy.1
      simpa [mul_comm] using this
    · have : ∫ y in x..x', Q y ≤ ∫ y in x..x', Q x' := by
        apply intervalIntegral.integral_mono_on hle (hint _ hx _ hx') intervalIntegrable_const
        intro y hy
        exact hm ⟨le_trans hx.1 hy.1, le_trans hy.2 hx'.2⟩ hx' hy.2
      rw [intervalIntegral.integral_symm]
      simp at this
      nlinarith
  linarith

lemma upd_mem {ι : Type*} [DecidableEq ι] {E : AuctionSetting} {θ : ι → ℝ}
    (hθ : θ ∈ E.typeSpace ι) (i : ι) {x : ℝ} (hx : x ∈ Set.Icc E.lo E.hi) :
    Function.update θ i x ∈ E.typeSpace ι := by
  intro j _
  by_cases hj : j = i
  · subst hj; simpa using hx
  · simp [Function.update_of_ne hj]; exact hθ j trivial

theorem auction_dsic_iff_core {ι : Type*} [Fintype ι] [DecidableEq ι] {E : AuctionSetting}
    (M : AuctionMechanism E ι) :
    M.IsDSIC ↔ ∀ i, ∀ θ ∈ E.typeSpace ι,
      MonotoneOn (fun x => M.q i (Function.update θ i x)) (Set.Icc E.lo E.hi) ∧
      ∀ x ∈ Set.Icc E.lo E.hi,
        M.t i (Function.update θ i x) =
          M.t i (Function.update θ i E.lo)
            + (x * M.q i (Function.update θ i x) - E.lo * M.q i (Function.update θ i E.lo))
            - ∫ y in E.lo..x, M.q i (Function.update θ i y) := by
  have hab : E.lo ≤ E.hi := E.lo_lt_hi.le
  constructor
  · intro h i θ hθ
    have habs : ICabs (fun x => M.q i (Function.update θ i x))
        (fun x => M.t i (Function.update θ i x)) E.lo E.hi := by
      intro x hx x' hx'
      have := h i (Function.update θ i x) (upd_mem hθ i hx) x' hx'
      simpa [Function.update_idem] using this
    refine ⟨abs_mono habs, fun x hx => ?_⟩
    have := abs_payoff habs hab hx
    linarith
  · intro h i θ hθ x hx
    obtain ⟨hm, hT⟩ := h i θ hθ
    have habs := abs_of_formula hm hT hab
    have := habs (θ i) ⟨hθ i trivial |>.1, hθ i trivial |>.2⟩ x hx
    simpa [Function.update_eq_self] using this

theorem auction_epir_iff_core {ι : Type*} [Fintype ι] [DecidableEq ι] {E : AuctionSetting}
    (M : AuctionMechanism E ι) (hM : M.IsDSIC) :
    M.IsEPIR ↔ ∀ i, ∀ θ ∈ E.typeSpace ι,
      M.t i (Function.update θ i E.lo) ≤ E.lo * M.q i (Function.update θ i E.lo) := by
  have hlo : E.lo ∈ Set.Icc E.lo E.hi := ⟨le_rfl, E.lo_lt_hi.le⟩
  constructor
  · intro h i θ hθ
    have := h i _ (upd_mem hθ i hlo)
    simp only [Function.update_self] at this
    linarith
  · intro h i θ hθ
    have h1 := hM i θ hθ E.lo hlo
    have h2 := h i θ hθ
    have hq := M.q_nonneg _ (upd_mem hθ i hlo) i
    have hθi : E.lo ≤ θ i := (hθ i trivial).1
    nlinarith

end MechanismDesign.DominantExamples

open MechanismDesign.DominantExamples


theorem solution {ι : Type*} [Fintype ι] [DecidableEq ι] {E : AuctionSetting}
    (M : AuctionMechanism E ι) :
    M.IsDSIC ↔ ∀ i, ∀ θ ∈ E.typeSpace ι,
      MonotoneOn (fun x => M.q i (Function.update θ i x)) (Set.Icc E.lo E.hi) ∧
      ∀ x ∈ Set.Icc E.lo E.hi,
        M.t i (Function.update θ i x) =
          M.t i (Function.update θ i E.lo)
            + (x * M.q i (Function.update θ i x) - E.lo * M.q i (Function.update θ i E.lo))
            - ∫ y in E.lo..x, M.q i (Function.update θ i y) := by
  exact auction_dsic_iff_core M
