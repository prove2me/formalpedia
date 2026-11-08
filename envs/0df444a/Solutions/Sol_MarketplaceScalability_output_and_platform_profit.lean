-- Prove2me | solution 1 for MarketplaceScalability.output_and_platform_profit
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T20:56:43.714797+00:00
-- url     : https://prove2.me/submissions/a8dc9880-8189-442d-9aa4-5245727daeb4

import Mathlib
import Definitions.Def_MarketplaceScalability_Model
import Definitions.Def_MarketplaceScalability_Params_piM
import Definitions.Def_MarketplaceScalability_Params_piO

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
theorem solution (M : Model) :
    StrictAntiOn M.q (Set.Ioc 0 M.cbar) ∧
    M.qm < M.qo ∧
    M.piM ≤ M.piO ∧
    (0 < M.α → M.piM < M.piO) := by
  have hJ : M.J = Set.Ioo 0 M.qbar := rfl
  have hanti : StrictAntiOn M.q (Set.Ioc 0 M.cbar) := by
    intro p1 hp1 p2 hp2 hlt
    obtain ⟨h1J, h1g⟩ := q_spec M p1 (M.range_foc p1 hp1)
    obtain ⟨h2J, h2g⟩ := q_spec M p2 (M.range_foc p2 hp2)
    by_contra hc
    push_neg at hc
    rcases hc.lt_or_eq with h | h
    · have := g_anti M h1J h2J h
      linarith
    · rw [h] at h1g
      linarith
  have hcown : M.cown ∈ Set.Ioc 0 M.cbar :=
    ⟨M.cown_pos, (M.cown_lt_c.trans M.c_lt_cbar).le⟩
  have hcbar : M.cbar ∈ Set.Ioc 0 M.cbar :=
    ⟨M.cown_pos.trans (M.cown_lt_c.trans M.c_lt_cbar), le_rfl⟩
  have hq : M.qm < M.qo := hanti hcown hcbar (M.cown_lt_c.trans M.c_lt_cbar)
  have hRmono : StrictMonoOn M.R M.J := by
    apply strictMonoOn_of_deriv_pos (by rw [hJ]; exact convex_Ioo 0 M.qbar)
    · intro x hx; exact (M.hasDerivAt_R x hx).continuousAt.continuousWithinAt
    · intro x hx
      rw [hJ, interior_Ioo] at hx
      rw [(M.hasDerivAt_R x hx).deriv]
      exact M.D_pos x hx
  have hmJ : M.qm ∈ M.J := (q_spec M _ (M.range_foc _ hcbar)).1
  have hoJ : M.qo ∈ M.J := (q_spec M _ (M.range_foc _ hcown)).1
  have hR : M.R M.qm < M.R M.qo := hRmono hmJ hoJ hq
  refine ⟨hanti, hq, ?_, ?_⟩
  · unfold Params.piM Params.piO
    exact mul_le_mul_of_nonneg_left hR.le M.alpha_nonneg
  · intro hα
    unfold Params.piM Params.piO
    exact mul_lt_mul_of_pos_left hR hα
