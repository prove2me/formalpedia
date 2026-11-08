-- Prove2me | solution 1 for MarketplaceScalability.hasDerivAt_pi
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T18:56:39.065942+00:00
-- url     : https://prove2.me/submissions/a7fefb56-37e6-4b91-a67e-eb590f8aa684

import Mathlib
import Definitions.Def_MarketplaceScalability_Model
import Definitions.Def_MarketplaceScalability_Params_pi

namespace Aux_MktQ

open MarketplaceScalability Filter Topology

theorem g_deriv (M : Model) (x : ℝ) (hx : x ∈ M.J) :
    HasDerivAt (fun x => (1 - M.α) * M.D x) ((1 - M.α) * deriv M.D x) x :=
  ((M.differentiableAt_D x hx).hasDerivAt).const_mul _

theorem g_anti (M : Model) : StrictAntiOn (fun x => (1 - M.α) * M.D x) M.J := by
  have hα : 0 < 1 - M.α := by linarith [M.alpha_lt_one]
  have hJ : M.J = Set.Ioo 0 M.qbar := rfl
  apply strictAntiOn_of_deriv_neg (by rw [hJ]; exact convex_Ioo 0 M.qbar)
  · intro x hx; exact (g_deriv M x hx).continuousAt.continuousWithinAt
  · intro x hx
    rw [hJ, interior_Ioo] at hx
    rw [(g_deriv M x hx).deriv]
    exact mul_neg_of_pos_of_neg hα (M.deriv_D_neg x hx)

theorem q_spec (M : Model) (y : ℝ) (h : ∃ x ∈ M.J, (1 - M.α) * M.D x = y) :
    M.q y ∈ M.J ∧ (1 - M.α) * M.D (M.q y) = y :=
  ⟨Function.invFunOn_mem h, Function.invFunOn_eq h⟩

theorem local_nhds (M : Model) {p : ℝ} (hp : p ∈ Set.Ioc 0 M.cbar) (a b : ℝ)
    (ha : a ∈ M.J) (hb : b ∈ M.J) (hax : a < M.q p) (hxb : M.q p < b) :
    ∀ᶠ y in 𝓝 p, (∃ x ∈ M.J, (1 - M.α) * M.D x = y) ∧ a < M.q y ∧ M.q y < b := by
  have hJ : M.J = Set.Ioo 0 M.qbar := rfl
  obtain ⟨hx0J, hgx0⟩ := q_spec M p (M.range_foc p hp)
  have hanti := g_anti M
  have h1 : (1 - M.α) * M.D b < p := by rw [← hgx0]; exact hanti hx0J hb hxb
  have h2 : p < (1 - M.α) * M.D a := by rw [← hgx0]; exact hanti ha hx0J hax
  filter_upwards [Ioo_mem_nhds h1 h2] with y hy
  have hIcc : Set.Icc a b ⊆ M.J := by
    intro z hz
    rw [hJ] at ha hb ⊢
    exact ⟨lt_of_lt_of_le ha.1 hz.1, lt_of_le_of_lt hz.2 hb.2⟩
  have hab : a ≤ b := (hax.trans hxb).le
  have hcont : ContinuousOn (fun x => (1 - M.α) * M.D x) (Set.Icc a b) :=
    fun z hz => (g_deriv M z (hIcc hz)).continuousAt.continuousWithinAt
  obtain ⟨x, hx, hgx⟩ := intermediate_value_Icc' hab hcont ⟨hy.1.le, hy.2.le⟩
  have hex : ∃ x ∈ M.J, (1 - M.α) * M.D x = y := ⟨x, hIcc hx, hgx⟩
  obtain ⟨hqJ, hgq⟩ := q_spec M y hex
  refine ⟨hex, ?_, ?_⟩
  · by_contra hc
    push_neg at hc
    have : (1 - M.α) * M.D a ≤ (1 - M.α) * M.D (M.q y) := hanti.antitoneOn hqJ ha hc
    linarith [hy.2]
  · by_contra hc
    push_neg at hc
    have : (1 - M.α) * M.D (M.q y) ≤ (1 - M.α) * M.D b := hanti.antitoneOn hb hqJ hc
    linarith [hy.1]

theorem hasDerivAt_q' (M : Model) {p : ℝ} (hp : p ∈ Set.Ioc 0 M.cbar) :
    HasDerivAt M.q ((1 - M.α) * deriv M.D (M.q p))⁻¹ p := by
  have hJ : M.J = Set.Ioo 0 M.qbar := rfl
  have hα : 0 < 1 - M.α := by linarith [M.alpha_lt_one]
  obtain ⟨hx0J, hgx0⟩ := q_spec M p (M.range_foc p hp)
  have hx0 : 0 < M.q p ∧ M.q p < M.qbar := by rw [hJ] at hx0J; exact hx0J
  have hcont : ContinuousAt M.q p := by
    rw [ContinuousAt, tendsto_order]
    constructor
    · intro a' ha'
      have hmem : max a' (M.q p / 2) ∈ M.J := by
        rw [hJ]; constructor
        · exact lt_of_lt_of_le (by linarith [hx0.1]) (le_max_right _ _)
        · exact max_lt (by linarith [hx0.2]) (by linarith [hx0.2, hx0.1])
      have hlt : max a' (M.q p / 2) < M.q p := max_lt ha' (by linarith [hx0.1])
      have hb : (M.q p + M.qbar) / 2 ∈ M.J := by rw [hJ]; constructor <;> linarith [hx0.1, hx0.2]
      filter_upwards [local_nhds M hp _ _ hmem hb hlt (by linarith [hx0.2])] with y hy
      exact lt_of_le_of_lt (le_max_left _ _) hy.2.1
    · intro b' hb'
      have hmem : min b' ((M.q p + M.qbar) / 2) ∈ M.J := by
        rw [hJ]; constructor
        · exact lt_min (by linarith [hx0.1]) (by linarith [hx0.1, hx0.2])
        · exact lt_of_le_of_lt (min_le_right _ _) (by linarith [hx0.2])
      have hlt : M.q p < min b' ((M.q p + M.qbar) / 2) := lt_min hb' (by linarith [hx0.2])
      have ha : M.q p / 2 ∈ M.J := by rw [hJ]; constructor <;> linarith [hx0.1, hx0.2]
      filter_upwards [local_nhds M hp _ _ ha hmem (by linarith [hx0.1]) hlt] with y hy
      exact lt_of_lt_of_le hy.2.2 (min_le_left _ _)
  have ha : M.q p / 2 ∈ M.J := by rw [hJ]; constructor <;> linarith [hx0.1, hx0.2]
  have hb : (M.q p + M.qbar) / 2 ∈ M.J := by rw [hJ]; constructor <;> linarith [hx0.1, hx0.2]
  have hev : ∀ᶠ y in 𝓝 p, (fun x => (1 - M.α) * M.D x) (M.q y) = y := by
    filter_upwards [local_nhds M hp _ _ ha hb (by linarith [hx0.1]) (by linarith [hx0.2])]
      with y hy
    exact (q_spec M y hy.1).2
  have hne : (1 - M.α) * deriv M.D (M.q p) ≠ 0 :=
    (mul_neg_of_pos_of_neg hα (M.deriv_D_neg _ hx0J)).ne
  exact HasDerivAt.of_local_left_inverse hcont (g_deriv M _ hx0J) hne hev

end Aux_MktQ

open MarketplaceScalability Aux_MktQ in
theorem solution (M : Model) {p : ℝ} (hp : p ∈ Set.Ioc 0 M.cbar) :
    HasDerivAt M.pi (M.q p + (p / (1 - M.α) - M.c) * deriv M.q p) p := by
  have hq := hasDerivAt_q' M hp
  obtain ⟨hx0J, hgx0⟩ := q_spec M p (M.range_foc p hp)
  have hα : 0 < 1 - M.α := by linarith [M.alpha_lt_one]
  have hR := (M.hasDerivAt_R (M.q p) hx0J).comp p hq
  have h := (hR.const_mul M.α).add (((hasDerivAt_id p).sub_const M.c).mul hq)
  have hD : M.D (M.q p) = p / (1 - M.α) := by
    field_simp
    linarith [hgx0]
  show HasDerivAt (fun y => M.α * M.R (M.q y) + (y - M.c) * M.q y) _ p
  refine h.congr_deriv ?_
  rw [hq.deriv, hD]
  simp only [id]
  field_simp
  ring
