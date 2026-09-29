-- Prove2me | solution 1 for LanglandsTunnell.eq_zero_of_deriv_eq_div_add_mul_of_re_pos_of_isBigO_pow
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/b9276df7-cd2e-5672-b31a-6a60223feb00

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_eq_zero_of_deriv_eq_div_add_mul_of_re_pos_of_isBigO_pow

set_option autoImplicit false

noncomputable section

namespace OsOde17

open Real Filter Topology

private def sol (α β : ℂ) (t : ℝ) : ℂ := Complex.exp (α * (Real.log t : ℂ) + β * (t : ℂ))

private theorem hasDerivAt_sol (α β : ℂ) {t : ℝ} (ht : t ≠ 0) :
    HasDerivAt (sol α β) ((α / t + β) * sol α β t) t := by
  have h1 : HasDerivAt (fun s : ℝ => (Real.log s : ℂ)) ((t : ℂ)⁻¹) t := by
    have h := (Real.hasDerivAt_log ht).ofReal_comp
    simpa [Complex.ofReal_inv] using h
  have h2 : HasDerivAt (fun s : ℝ => (s : ℂ)) 1 t := by
    simpa using (hasDerivAt_id t).ofReal_comp
  have h3 : HasDerivAt (fun s : ℝ => α * (Real.log s : ℂ) + β * (s : ℂ)) (α * (t : ℂ)⁻¹ + β * 1) t :=
    (h1.const_mul α).add (h2.const_mul β)
  have h4 := h3.cexp
  unfold sol
  convert h4 using 1
  rw [div_eq_mul_inv, mul_one, mul_comm]

private theorem sol_ne_zero (α β : ℂ) (t : ℝ) : sol α β t ≠ 0 := Complex.exp_ne_zero _

private theorem norm_sol (α β : ℂ) {t : ℝ} (ht : 0 < t) : ‖sol α β t‖ = t ^ α.re * Real.exp (β.re * t) := by
  unfold sol
  rw [Complex.norm_exp, Complex.add_re, Real.exp_add, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero, Real.rpow_def_of_pos ht, mul_comm (Real.log t)]

private theorem exists_eq_const_mul_sol (α β : ℂ) (f : ℝ → ℂ)
    (hf : ∀ t : ℝ, 0 < t → HasDerivAt f ((α / t + β) * f t) t) :
    ∃ c : ℂ, ∀ t : ℝ, 0 < t → f t = c * sol α β t := by
  set g : ℝ → ℂ := fun t => f t / sol α β t with hg
  have hgd : ∀ t : ℝ, 0 < t → HasDerivAt g 0 t := by
    intro t ht
    have h := (hf t ht).div (hasDerivAt_sol α β ht.ne') (sol_ne_zero α β t)
    convert h using 1
    · rfl
    · rfl
    ring
  refine ⟨g 1, fun t ht => ?_⟩
  have hconst : g t = g 1 := by
    refine isOpen_Ioi.is_const_of_fderiv_eq_zero (𝕜 := ℝ) (f := g) isPreconnected_Ioi
      (fun s hs => (hgd s hs).differentiableAt.differentiableWithinAt) (fun s hs => ?_) ht (Set.mem_Ioi.mpr one_pos)
    rw [(hgd s hs).hasFDerivAt.fderiv]
    ext
    simp
  rw [← hconst, hg]
  field_simp [sol_ne_zero α β t]

private theorem main (α β : ℂ) (hβ : 0 < β.re) (f : ℝ → ℂ)
    (hf : DifferentiableOn ℝ f (Set.Ioi 0))
    (hfeq : ∀ t : ℝ, 0 < t → deriv f t = (α / (t : ℂ) + β) * f t)
    (C : ℝ) (N : ℕ) (hgrowth : ∀ t : ℝ, 1 ≤ t → ‖f t‖ ≤ C * t ^ N) :
    ∀ t : ℝ, 0 < t → f t = 0 := by
  have hf' : ∀ t : ℝ, 0 < t → HasDerivAt f ((α / t + β) * f t) t := by
    intro t ht
    rw [← hfeq t ht]
    exact (hf.differentiableAt (Ioi_mem_nhds ht)).hasDerivAt
  obtain ⟨c, hc⟩ := exists_eq_const_mul_sol α β f hf'
  suffices hc0 : c = 0 by intro t ht; rw [hc t ht, hc0, zero_mul]
  by_contra hc0
  have hlim : Tendsto (fun x : ℝ => Real.exp (β.re * x) / x ^ ((N : ℝ) - α.re)) atTop atTop :=
    tendsto_exp_mul_div_rpow_atTop ((N : ℝ) - α.re) β.re hβ
  have hev := (hlim.eventually (eventually_gt_atTop (C / ‖c‖))).and (eventually_ge_atTop (1 : ℝ))
  obtain ⟨x, hx, hx1⟩ := hev.exists
  have hxpos : 0 < x := lt_of_lt_of_le one_pos hx1
  have hb := hgrowth x hx1
  rw [hc x hxpos, norm_mul, norm_sol α β hxpos, ← Real.rpow_natCast] at hb
  have hcpos : 0 < ‖c‖ := norm_pos_iff.mpr hc0
  have hxr : 0 < x ^ ((N : ℝ) - α.re) := Real.rpow_pos_of_pos hxpos _
  have hxa : 0 < x ^ α.re := Real.rpow_pos_of_pos hxpos _
  have h1 : C * x ^ ((N : ℝ) - α.re) < ‖c‖ * Real.exp (β.re * x) := by
    have h := (lt_div_iff₀ hxr).mp hx
    rw [div_mul_eq_mul_div, div_lt_iff₀ hcpos] at h
    linarith [mul_comm (Real.exp (β.re * x)) ‖c‖]
  have h2 : C * x ^ (N : ℝ) < ‖c‖ * (x ^ α.re * Real.exp (β.re * x)) := by
    have h3 := mul_lt_mul_of_pos_right h1 hxa
    have hsplit : x ^ (N : ℝ) = x ^ ((N : ℝ) - α.re) * x ^ α.re := by
      rw [← Real.rpow_add hxpos]; ring_nf
    rw [hsplit]
    nlinarith [h3]
  linarith

end OsOde17

end

theorem solution
    (α β : ℂ) (hβ : 0 < β.re) (f : ℝ → ℂ)
    (hf : DifferentiableOn ℝ f (Set.Ioi 0))
    (hfeq : ∀ t : ℝ, 0 < t → deriv f t = (α / (t : ℂ) + β) * f t)
    (C : ℝ) (N : ℕ) (hgrowth : ∀ t : ℝ, 1 ≤ t → ‖f t‖ ≤ C * t ^ N) :
    ∀ t : ℝ, 0 < t → f t = 0 :=
  OsOde17.main α β hβ f hf hfeq C N hgrowth

end S_LanglandsTunnell_eq_zero_of_deriv_eq_div_add_mul_of_re_pos_of_isBigO_pow
end P2MW
export P2MW.S_LanglandsTunnell_eq_zero_of_deriv_eq_div_add_mul_of_re_pos_of_isBigO_pow (solution)
