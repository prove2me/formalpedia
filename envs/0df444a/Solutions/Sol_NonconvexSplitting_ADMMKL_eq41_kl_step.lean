-- Prove2me | solution 1 for NonconvexSplitting.ADMMKL.eq41_kl_step
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T12:46:58.837289+00:00
-- url     : https://prove2.me/submissions/80a946e1-42f5-4ddd-9f0a-01d1c5a43d4f

import Mathlib.Analysis.Convex.Deriv
import Mathlib.Tactic
import Definitions.Def_NonconvexSplitting_ADMMKL_AugLagProd
import Definitions.Def_NonconvexSplitting_ADMMKL_KLProperty
open Filter Topology NonconvexSplitting.Shared NonconvexSplitting.ADMMKL
open scoped RealInnerProductSpace

theorem solution {n m : ℕ} (h : EuclideanSpace ℝ (Fin n) → ℝ) (P : EuclideanSpace ℝ (Fin m) → EReal)
    (M : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m)) (β : ℝ)
    (x : ℕ → EuclideanSpace ℝ (Fin n)) (y z : ℕ → EuclideanSpace ℝ (Fin m))
    (C D : ℝ) (hC : 0 < C) (hD : 0 < D)
    (h35 : ∀ t : ℕ, 1 ≤ t →
      ∃ w ∈ LimitingSubdiff (augLagX h P M β) (pack (x (t + 1)) (y (t + 1)) (z (t + 1))),
        ‖w‖ ≤ C * ‖x (t + 1) - x t‖)
    (h36 : ∀ t : ℕ, 1 ≤ t →
      augLag h P M β (x (t + 1)) (y (t + 1)) (z (t + 1)) + ((D * ‖x (t + 1) - x t‖ ^ 2 : ℝ) : EReal) ≤
        augLag h P M β (x t) (y t) (z t))
    (lstar : ℝ) (hgt : ∀ t : ℕ, 1 ≤ t → (lstar : EReal) < augLag h P M β (x t) (y t) (z t))
    (η : ℝ) (hη : 0 < η) (V : Set (XYZ n m)) (φ : ℝ → ℝ) (hφ : IsDesingularizer η φ)
    (h40 : ∀ w ∈ V, (lstar : EReal) < augLagX h P M β w →
      augLagX h P M β w < (lstar : EReal) + (η : EReal) →
      ∀ v ∈ LimitingSubdiff (augLagX h P M β) w,
        1 ≤ deriv φ (augLagX h P M β w - (lstar : EReal)).toReal * ‖v‖)
    (t : ℕ) (ht : 2 ≤ t) (hV : pack (x t) (y t) (z t) ∈ V)
    (hlo : (lstar : EReal) < augLag h P M β (x t) (y t) (z t))
    (hhi : augLag h P M β (x t) (y t) (z t) < (lstar : EReal) + (η : EReal)) :
    ‖x (t + 1) - x t‖ + (‖x (t + 1) - x t‖ - ‖x t - x (t - 1)‖) ≤
      C / D * (φ (augLag h P M β (x t) (y t) (z t) - (lstar : EReal)).toReal -
        φ (augLag h P M β (x (t + 1)) (y (t + 1)) (z (t + 1)) - (lstar : EReal)).toReal) := by
  let L := fun k => augLag h P M β (x k) (y k) (z k)
  have hbot : L t ≠ ⊥ := ne_bot_of_gt hlo
  have htop : L t ≠ ⊤ := ne_top_of_lt hhi
  have hd := h36 t (by omega)
  have hd0 : (0:EReal) ≤ ↑(D*‖x (t+1)-x t‖^2) := by exact_mod_cast mul_nonneg hD.le (sq_nonneg _)
  have hle : L (t+1) ≤ L t := (le_add_of_nonneg_right hd0).trans hd
  have hb1 : L (t+1) ≠ ⊥ := ne_bot_of_gt (hgt (t+1) (by omega))
  have ht1 : L (t+1) ≠ ⊤ := ne_top_of_lt (hle.trans_lt hhi)
  let a := (L t).toReal
  let b := (L (t+1)).toReal
  have he : L t = (a:EReal) := (EReal.coe_toReal htop hbot).symm
  have he1 : L (t+1) = (b:EReal) := (EReal.coe_toReal ht1 hb1).symm
  change L (t+1)+_ ≤ L t at hd
  rw [he,he1,← EReal.coe_add,EReal.coe_le_coe_iff] at hd
  have ha0 : 0 < a-lstar := by
    change (lstar:EReal)<L t at hlo
    rw [he,EReal.coe_lt_coe_iff] at hlo
    linarith
  have haη : a-lstar<η := by
    change L t<(lstar:EReal)+↑η at hhi
    rw [he,← EReal.coe_add,EReal.coe_lt_coe_iff] at hhi
    linarith
  have hb0 : 0 < b-lstar := by
    have hh := hgt (t+1) (by omega)
    change (lstar:EReal)<L (t+1) at hh
    rw [he1,EReal.coe_lt_coe_iff] at hh
    linarith
  have hab : b ≤ a := by nlinarith only [hd,hD,sq_nonneg ‖x (t+1)-x t‖]
  have hbη : b-lstar<η := by linarith
  have hp := hφ.2.2.2.2.2 (a-lstar) ⟨ha0,haη⟩
  have hc : deriv φ (a-lstar)*(a-b) ≤ φ (a-lstar)-φ (b-lstar) := by
    rcases eq_or_lt_of_le hab with hh|hh
    · simp [hh]
    · have hh := hφ.2.1.deriv_le_slope ⟨hb0.le,hbη⟩ ⟨ha0.le,haη⟩
        (show b-lstar<a-lstar by linarith) (differentiableAt_of_deriv_ne_zero hp.ne')
      rw [slope_def_field] at hh
      have hmul := (le_div_iff₀ (show 0<a-lstar-(b-lstar) by linarith)).mp hh
      convert! hmul using 1 <;> ring
  obtain ⟨w,hw,hwbound⟩ := h35 (t-1) (by omega)
  rw [Nat.sub_add_cancel (by omega : 1 ≤ t)] at hw hwbound
  have hkl := h40 (pack (x t) (y t) (z t)) hV hlo hhi w hw
  change 1 ≤ deriv φ (L t-(lstar:EReal)).toReal*‖w‖ at hkl
  rw [he,← EReal.coe_sub,EReal.toReal_coe] at hkl
  have hkl1 : 1 ≤ deriv φ (a-lstar)*(C*‖x t-x (t-1)‖) :=
    hkl.trans (mul_le_mul_of_nonneg_left hwbound hp.le)
  have hprev : 0 < ‖x t-x (t-1)‖ := by
    by_contra hh
    have he0 : ‖x t-x (t-1)‖=0 := le_antisymm (le_of_not_gt hh) (norm_nonneg _)
    norm_num [he0] at hkl1
  have hcd : deriv φ (a-lstar)*(D*‖x (t+1)-x t‖^2) ≤ φ (a-lstar)-φ (b-lstar) :=
    (mul_le_mul_of_nonneg_left (show D*‖x (t+1)-x t‖^2≤a-b by linarith) hp.le).trans hc
  have hkey : D*‖x (t+1)-x t‖^2 ≤ C*‖x t-x (t-1)‖*(φ (a-lstar)-φ (b-lstar)) := by
    have h1 := mul_le_mul_of_nonneg_right hkl1 (mul_nonneg hD.le (sq_nonneg ‖x (t+1)-x t‖))
    have h2 := mul_le_mul_of_nonneg_left hcd (mul_nonneg hC.le hprev.le)
    nlinarith only [h1,h2]
  have hsq := mul_nonneg hD.le (sq_nonneg (‖x (t+1)-x t‖-‖x t-x (t-1)‖))
  have hfin : D*(2*‖x (t+1)-x t‖-‖x t-x (t-1)‖) ≤ C*(φ (a-lstar)-φ (b-lstar)) := by
    apply (mul_le_mul_iff_left₀ hprev).mp
    nlinarith only [hkey,hsq]
  change _ ≤ C/D*(φ (L t-(lstar:EReal)).toReal-φ (L (t+1)-(lstar:EReal)).toReal)
  rw [he,he1,← EReal.coe_sub,← EReal.coe_sub,EReal.toReal_coe,EReal.toReal_coe]
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ hD).mpr
  convert! hfin using 1 <;> ring
