-- Prove2me | solution 1 for NonconvexDRS.Tight.thm_4_8_identity
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T12:48:00.974731+00:00
-- url     : https://prove2.me/submissions/216a2e34-963d-469e-b459-90feb23ee544

import Mathlib
import Definitions.Def_NonconvexDRS_Tight_Setting

set_option autoImplicit false
open Filter Topology NonconvexDRS.Tight

theorem solution (L σ γ lam p : ℝ) (hL : 0 < L) (hσ : -L ≤ σ ∧ σ ≤ L) (hp : 1 < p)
    (hγ : 0 < γ) (hγL : γ * L < 1) (hlam : 0 < lam)
    (s u v : ℕ → ℝ) (hrun : IsDRSRun (phi1Ex L σ 1) (indic ({p} : Set ℝ)) γ lam s u v)
    (k : ℕ) (hk : 1 < u k) (hk1 : 1 < u (k + 1)) :
    |u (k + 1) - p| = |1 - lam / (1 + γ * σ)| * |u k - p| ∧
    (2 * (1 + γ * σ) ≤ lam → |u k - p| ≤ |u (k + 1) - p|) := by
  have hpos : 0 < 1 + γ * σ := by nlinarith [hσ.1]
  -- v j = p
  have hv : ∀ j, v j = p := by
    intro j
    by_contra hne
    have h := (hrun j).2.1 p
    have e1 : indic ({p} : Set ℝ) (v j) = ⊤ := by simp [indic, hne]
    have e2 : indic ({p} : Set ℝ) p = 0 := by simp [indic]
    rw [e1, e2, zero_add] at h
    rw [EReal.top_add_of_ne_bot (EReal.coe_ne_bot _)] at h
    exact absurd h (not_le.2 (EReal.coe_lt_top _))
  -- stationarity
  have hstat : ∀ j, 1 < u j → s j = (1 + γ * σ) * u j + γ * (L - σ) := by
    intro j hj
    have hmem := (hrun j).1
    set q : ℝ → ℝ := fun w => L / 2 * w ^ 2 - (L - σ) / 2 * (w - 1) ^ 2 + (w - s j) ^ 2 / (2 * γ) with hq
    have hmin : IsLocalMin q (u j) := by
      have hev : ∀ᶠ w in 𝓝 (u j), 1 < w := Ioi_mem_nhds hj
      filter_upwards [hev] with w hw
      have h := hmem w
      simp only [phi1Ex, Real.norm_eq_abs, sq_abs] at h
      rw [if_neg (not_le.2 hj), if_neg (not_le.2 hw), ← EReal.coe_add, ← EReal.coe_add,
        EReal.coe_le_coe_iff] at h
      simp only [hq]
      linarith
    have hder : HasDerivAt q (L * u j - (L - σ) * (u j - 1) + (u j - s j) / γ) (u j) := by
      have h1 := (hasDerivAt_pow 2 (u j)).const_mul (L / 2)
      have h2 := (((hasDerivAt_id (u j)).sub_const 1).pow 2).const_mul ((L - σ) / 2)
      have h3 := (((hasDerivAt_id (u j)).sub_const (s j)).pow 2).div_const (2 * γ)
      refine ((h1.sub h2).add h3).congr_deriv ?_
      norm_num
      field_simp
    have h0 := hmin.hasDerivAt_eq_zero hder
    field_simp at h0
    nlinarith [h0]
  have hs1 := hstat k hk
  have hs2 := hstat (k + 1) hk1
  have hstep := (hrun k).2.2
  rw [hv k, smul_eq_mul] at hstep
  have hkey : (1 + γ * σ) * (u (k + 1) - p) = ((1 + γ * σ) - lam) * (u k - p) := by
    nlinarith [hs1, hs2, hstep]
  have hfac : u (k + 1) - p = (1 - lam / (1 + γ * σ)) * (u k - p) := by
    field_simp
    nlinarith [hkey]
  have habs : |u (k + 1) - p| = |1 - lam / (1 + γ * σ)| * |u k - p| := by
    rw [hfac, abs_mul]
  refine ⟨habs, fun h2 => ?_⟩
  rw [habs]
  have : lam / (1 + γ * σ) ≥ 2 := by
    rw [ge_iff_le, le_div_iff₀ hpos]; linarith
  have : 1 ≤ |1 - lam / (1 + γ * σ)| := by
    rw [abs_of_nonpos (by linarith)]; linarith
  exact le_mul_of_one_le_left (abs_nonneg _) this
