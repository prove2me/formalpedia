-- Prove2me | solution 1 for MarketplaceScalability.profit_jump
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-10T05:59:16.073728+00:00
-- url     : https://prove2.me/submissions/0d8885b4-bed2-4179-b2a8-02bda772ec46

import Mathlib
import Definitions.Def_MarketplaceScalability_Model
import Definitions.Def_MarketplaceScalability_Params_piN
import Definitions.Def_MarketplaceScalability_Params_qm

namespace Aux_MSPJ

open Set in
lemma Rbound (R D : ℝ → ℝ) (a b : ℝ) (hab : a < b)
    (hR : ∀ x ∈ Ioo a b, HasDerivAt R (D x) x) (hD : ∀ x ∈ Ioo a b, 0 < D x)
    (hanti : AntitoneOn D (Ioo a b)) :
    ∀ x ∈ Ioo a b, R x ≤ R ((a + b) / 2) + D ((a + b) / 2) * (b - a) := by
  intro x hx
  obtain ⟨m, hmdef⟩ : ∃ m, m = (a + b) / 2 := ⟨_, rfl⟩
  rw [← hmdef]
  have hm : m ∈ Ioo a b := ⟨by rw [hmdef]; linarith, by rw [hmdef]; linarith⟩
  have hsub : ∀ y z, y ∈ Ioo a b → z ∈ Ioo a b → ∀ t ∈ Icc y z, t ∈ Ioo a b :=
    fun y z hy hz t ht => ⟨by linarith [hy.1, ht.1], by linarith [hz.2, ht.2]⟩
  have hcont : ∀ y z, y ∈ Ioo a b → z ∈ Ioo a b → ContinuousOn R (Icc y z) :=
    fun y z hy hz t ht => (hR t (hsub y z hy hz t ht)).continuousAt.continuousWithinAt
  have hDm := hD m hm
  rcases lt_trichotomy x m with h | h | h
  · obtain ⟨ξ, hξ, hξe⟩ := exists_hasDerivAt_eq_slope R D h (hcont x m hx hm)
      (fun t ht => hR t (hsub x m hx hm t (Ioo_subset_Icc_self ht)))
    have hξJ := hsub x m hx hm ξ (Ioo_subset_Icc_self hξ)
    have hDξ := hD ξ hξJ
    rw [eq_div_iff (by linarith)] at hξe
    nlinarith [mul_pos hDξ (sub_pos.2 h), mul_pos hDm (sub_pos.2 hab)]
  · rw [h]; nlinarith [mul_pos hDm (sub_pos.2 hab)]
  · obtain ⟨ξ, hξ, hξe⟩ := exists_hasDerivAt_eq_slope R D h (hcont m x hm hx)
      (fun t ht => hR t (hsub m x hm hx t (Ioo_subset_Icc_self ht)))
    have hξJ := hsub m x hm hx ξ (Ioo_subset_Icc_self hξ)
    have hle : D ξ ≤ D m := hanti hm hξJ hξ.1.le
    rw [eq_div_iff (by linarith)] at hξe
    have h1 : D ξ * (x - m) ≤ D m * (x - m) := mul_le_mul_of_nonneg_right hle (by linarith)
    have h2 : D m * (x - m) ≤ D m * (b - a) :=
      mul_le_mul_of_nonneg_left (by linarith [hx.2, hm.1]) hDm.le
    linarith

end Aux_MSPJ

open MarketplaceScalability in
theorem solution (M : Model) :
    M.pi M.cbar - M.piM = (M.cbar - M.c) * M.qm ∧
    0 < (M.cbar - M.c) * M.qm ∧
    M.piM < sSup (M.piN '' Set.Ioi 0) ∧
    ∀ p ∈ Set.Ioi 0, IsMaxOn M.piN (Set.Ioi 0) p → p ∈ Set.Ioc 0 M.cbar := by
  have hc0 : 0 < M.cbar := by linarith [M.cown_pos, M.cown_lt_c, M.c_lt_cbar]
  have hqJ : ∀ p ∈ Set.Ioc 0 M.cbar, M.q p ∈ M.J := by
    intro p hp
    obtain ⟨x, hx, hxp⟩ := M.range_foc p hp
    have hex : ∃ a ∈ M.J, (fun x => (1 - M.α) * M.D x) a = p := ⟨x, hx, hxp⟩
    unfold Params.q
    exact Function.invFunOn_mem hex
  have hqm : M.qm ∈ M.J := hqJ M.cbar ⟨hc0, le_rfl⟩
  have hqm0 : 0 < M.qm := hqm.1
  have h1 : M.pi M.cbar - M.piM = (M.cbar - M.c) * M.qm := by
    unfold Params.pi Params.piM Params.qm; ring
  have h2 : 0 < (M.cbar - M.c) * M.qm := mul_pos (by linarith [M.c_lt_cbar]) hqm0
  have hN : M.piN M.cbar = M.pi M.cbar := by unfold Params.piN; rw [if_pos le_rfl]
  have hgt : M.piM < M.piN M.cbar := by rw [hN]; linarith
  refine ⟨h1, h2, ?_, ?_⟩
  · have hJ : M.J = Set.Ioo 0 M.qbar := rfl
    have hanti : AntitoneOn M.D (Set.Ioo 0 M.qbar) := by
      apply StrictAntiOn.antitoneOn
      apply strictAntiOn_of_deriv_neg (convex_Ioo 0 M.qbar)
      · intro x hx
        exact (M.differentiableAt_D x (hJ ▸ hx)).continuousAt.continuousWithinAt
      · intro x hx
        rw [interior_Ioo] at hx
        exact M.deriv_D_neg x (hJ ▸ hx)
    obtain ⟨B, hBdef⟩ : ∃ B, B = M.R ((0 + M.qbar) / 2) + M.D ((0 + M.qbar) / 2) * (M.qbar - 0) :=
      ⟨_, rfl⟩
    have hB : ∀ x ∈ M.J, M.R x ≤ B := by
      intro x hx
      rw [hBdef]
      exact Aux_MSPJ.Rbound M.R M.D 0 M.qbar M.qbar_pos (fun y hy => M.hasDerivAt_R y (hJ ▸ hy))
        (fun y hy => M.D_pos y (hJ ▸ hy)) hanti x (hJ ▸ hx)
    have hbdd : BddAbove (M.piN '' Set.Ioi 0) := by
      refine ⟨max (M.α * B + (M.cbar + |M.c|) * M.qbar) M.piM, ?_⟩
      rintro y ⟨p, hp, rfl⟩
      unfold Params.piN
      split_ifs with h
      · apply le_max_of_le_left
        have hq := hqJ p ⟨hp, h⟩
        have hRq := hB _ hq
        have hq1 : 0 < M.q p := hq.1
        have hq2 : M.q p < M.qbar := hq.2
        unfold Params.pi
        have e1 : M.α * M.R (M.q p) ≤ M.α * B := mul_le_mul_of_nonneg_left hRq M.alpha_nonneg
        have e2 : (p - M.c) * M.q p ≤ (M.cbar + |M.c|) * M.q p :=
          mul_le_mul_of_nonneg_right (by linarith [neg_abs_le M.c]) hq1.le
        have e3 : (M.cbar + |M.c|) * M.q p ≤ (M.cbar + |M.c|) * M.qbar :=
          mul_le_mul_of_nonneg_left hq2.le (by linarith [abs_nonneg M.c])
        linarith
      · exact le_max_right _ _
    exact lt_of_lt_of_le hgt (le_csSup hbdd ⟨M.cbar, hc0, rfl⟩)
  · intro p hp hmax
    refine ⟨hp, ?_⟩
    by_contra h
    push_neg at h
    have hle := isMaxOn_iff.mp hmax M.cbar hc0
    have hp' : M.piN p = M.piM := by unfold Params.piN; rw [if_neg (not_le.mpr h)]
    linarith
