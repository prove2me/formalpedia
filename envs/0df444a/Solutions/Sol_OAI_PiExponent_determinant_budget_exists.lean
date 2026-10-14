-- Prove2me | solution 1 for OAI.PiExponent.determinant_budget_exists
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-14T08:44:15.691862+00:00
-- url     : https://prove2.me/submissions/5ffe0661-a0bf-4e2a-9970-c0d2625e7928
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_PiExponent_DeterminantSetup
import Theorems.Thm_OAI_PiExponent_quadratic_gap_window
import Theorems.Thm_OAI_PiExponent_balanced_center_amplification
import Theorems.Thm_OAI_PiExponent_rational_scale_error_control
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

theorem solution (nu : ℝ) (hnu : 2 < nu) :
    Nonempty (OAI.PiExponent.DeterminantBudget nu) := by
  obtain ⟨theta, A, eta, ht, ht1, hA, hA1, he, he1, hquad, hgap⟩ :=
    OAI.PiExponent.quadratic_gap_window nu hnu
  have htR : 0 < (theta : ℝ) := by exact_mod_cast ht
  have hnuR : 0 < nu := by linarith only [hnu]
  let g : ℝ :=
    nu * (A * (1 - eta) - (theta : ℝ)) - (1 - (theta : ℝ))
  have hg : 0 < g := hgap

  -- First separate the fixed error from the positive slack.
  obtain ⟨F, hF⟩ := exists_nat_gt
    (max (2 / (theta : ℝ)) (4 * nu / g))
  have hFtheta : 2 / (theta : ℝ) < (F : ℝ) :=
    lt_of_le_of_lt (le_max_left _ _) hF
  have hFnu : 4 * nu / g < (F : ℝ) :=
    lt_of_le_of_lt (le_max_right _ _) hF
  have hFpos : 0 < (F : ℝ) :=
    lt_trans (div_pos (by norm_num) htR) hFtheta
  let a : ℝ := nu / (F : ℝ)
  have ha : 0 ≤ a := by
    dsimp only [a]
    exact (div_pos hnuR hFpos).le
  have ha_gap : a < g / 4 := by
    have hmul : 4 * nu < (F : ℝ) * g :=
      (div_lt_iff₀ hg).mp hFnu
    dsimp only [a]
    apply (div_lt_iff₀ hFpos).mpr
    nlinarith only [hmul]

  -- Balanced centers amplify the collision coefficient.
  let L : ℝ := (Real.log 2 / 4) * eta ^ 2
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hL : 0 < L := by
    dsimp only [L]
    positivity
  let R : ℝ := 4 * (1 + g) / g
  let p : ℝ := (R / L) * ((4 * Real.log 2) * (F : ℝ))
  let q : ℝ := (R / L) * (2 * Real.log 2 + 200)
  obtain ⟨m, K, hm, hK, hbalance, hamplify⟩ :=
    OAI.PiExponent.balanced_center_amplification
      theta A p q ht ht1 hA hquad
  have hKR : 0 < (K : ℝ) := by exact_mod_cast hK
  have hKone : (1 : ℝ) ≤ (K : ℝ) := by
    exact_mod_cast (Nat.succ_le_of_lt hK)
  have htransR : (K : ℝ) * (theta : ℝ) ^ m < 1 := by
    have hnonneg : 0 ≤ (K : ℝ) * (theta : ℝ) ^ m := by positivity
    have hprod := mul_nonneg (sub_nonneg.mpr hKone) hnonneg
    nlinarith only [hbalance, hprod]
  have htrans : (K : ℚ) * theta ^ m < 1 := by
    exact_mod_cast htransR

  let b : ℝ := (4 * Real.log 2) * (F : ℝ) * (m : ℝ) + 2 * Real.log 2
  let c : ℝ := L * ((K : ℝ) * (theta : ℝ) ^ m /
    (((m : ℝ) + 1) * A ^ m))
  have hcapacity : R * (b + 200) < c := by
    have hscaled := mul_lt_mul_of_pos_left hamplify hL
    change L * (p * (m : ℝ) + q) < c at hscaled
    have hcancel : L * (R / L) = R := mul_div_cancel₀ R (ne_of_gt hL)
    calc
      R * (b + 200) = (L * (R / L)) * (b + 200) := by rw [hcancel]
      _ = L * (p * (m : ℝ) + q) := by
        dsimp only [p, q, b]
        ring
      _ < c := hscaled
  have hcapacity' : 4 * (b + 2 * (100 : ℝ)) * (1 + g) / g < c := by
    calc
      4 * (b + 2 * (100 : ℝ)) * (1 + g) / g = R * (b + 200) := by
        dsimp only [R]
        ring
      _ < c := hcapacity

  -- The remaining logarithmic coefficient is nonnegative.
  let d : ℝ :=
    (4 * Real.log 2) * (m : ℝ) + (theta : ℝ) + Real.log 4 +
      Real.log (2 * (K : ℝ)) + nu + Real.log (200 * (K : ℝ))
  have hlog4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hlog2K : 0 ≤ Real.log (2 * (K : ℝ)) :=
    Real.log_nonneg (by linarith only [hKone])
  have hlog200K : 0 ≤ Real.log (200 * (K : ℝ)) :=
    Real.log_nonneg (by linarith only [hKone])
  have hb : 0 ≤ b := by
    dsimp only [b]
    positivity
  have hd : 0 ≤ d := by
    dsimp only [d]
    positivity

  obtain ⟨v0, w0, wmin, hv, hw, hn, hvolume, hE0, hEg, hEc⟩ :=
    OAI.PiExponent.rational_scale_error_control
      theta m K a b 100 d g c hK ht hbalance ha ha_gap hb
      (by norm_num) hd hg hcapacity'
  let E : ℝ :=
    a + b / (v0 : ℝ) + 100 * (K : ℝ) / (w0 : ℝ) + d / (wmin : ℝ)
  have hvR : 0 < (v0 : ℝ) := by exact_mod_cast hv
  have hmplus : ((m : ℝ) + 1) ≠ 0 := by positivity
  have hApow : A ^ m ≠ 0 := ne_of_gt (pow_pos hA m)
  have hcollision :
      c / (v0 : ℝ) = (Real.log 2 / 4) *
        (eta ^ 2 * (K : ℝ) * (theta : ℝ) ^ m /
          (((m : ℝ) + 1) * (v0 : ℝ) * A ^ m)) := by
    dsimp only [c, L]
    field_simp [ne_of_gt hvR, hmplus, hApow]
    <;> ring

  refine ⟨{
    m := m
    K := K
    w0 := w0
    v0 := v0
    theta := theta
    A := A
    eta := eta
    F0 := (F : ℝ)
    wmin := wmin
    E := E
    m_pos := hm
    K_pos := hK
    w0_pos := hw
    v0_pos := hv
    theta_pos := ht
    theta_lt_one := ht1
    volume_transverse := htrans
    volume_full := hvolume
    A_pos := hA
    A_lt_one := hA1
    eta_pos := he
    eta_lt_one := he1
    F0_pos := hFpos
    F0_large := hFtheta
    wmin_pos := hn
    E_nonneg := hE0
    E_eq := by rfl
    gap_pos := hg
    error_gap := hEg
    collision_gap := ?_
  }⟩
  rw [← hcollision]
  exact hEc