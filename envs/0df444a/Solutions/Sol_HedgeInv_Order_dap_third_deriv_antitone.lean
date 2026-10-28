-- Prove2me | solution 1 for HedgeInv.Order.dap_third_deriv_antitone
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T03:08:21.25057+00:00
-- url     : https://prove2.me/submissions/7848b776-fe7f-4d5e-89fd-0a56f9788233

import Mathlib
import Definitions.Def_HedgeInv_Order_Model

open HedgeInv.Order in
theorem solution (u : ℝ → ℝ) (hu : ContDiff ℝ 3 u)
    (hu1 : ∀ w, 0 < deriv u w) (hu2 : ∀ w, deriv (deriv u) w < 0)
    (hDAP : Antitone (absPrudence u)) :
    Antitone (deriv (deriv (deriv u))) := by
  obtain ⟨hd1, -, hc2⟩ := contDiff_succ_iff_deriv.mp (hu.of_le (by norm_num) : ContDiff ℝ (2+1) u)
  obtain ⟨hd2, -, hc1⟩ := contDiff_succ_iff_deriv.mp (hc2.of_le (by norm_num) : ContDiff ℝ (1+1) (deriv u))
  obtain ⟨hd3, -, -⟩ := contDiff_succ_iff_deriv.mp (hc1.of_le (by norm_num) : ContDiff ℝ (0+1) (deriv (deriv u)))
  set g : ℝ → ℝ := fun w => -deriv (deriv u) w with hg
  have gpos : ∀ w, 0 < g w := fun w => by simp only [hg]; linarith [hu2 w]
  have gd : ∀ w, HasDerivAt g (-deriv (deriv (deriv u)) w) w := fun w => (hd3 w).hasDerivAt.neg
  set f : ℝ → ℝ := fun w => Real.log (g w) with hf
  have fd : ∀ w, HasDerivAt f (-deriv (deriv (deriv u)) w / g w) w :=
    fun w => (gd w).log (gpos w).ne'
  have fderiv : ∀ w, deriv f w = -absPrudence u w := by
    intro w
    rw [(fd w).deriv]
    simp only [hg]
    unfold absPrudence
    rw [neg_div_neg_eq, neg_div, neg_neg]
  have fmono : Monotone (deriv f) := by
    intro x y hxy
    rw [fderiv x, fderiv y]
    linarith [hDAP hxy]
  have fconv : ConvexOn ℝ Set.univ f :=
    Monotone.convexOn_univ_of_deriv (fun w => (fd w).differentiableAt) fmono
  have gconv : ConvexOn ℝ Set.univ g := by
    refine ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩
    calc g (a • x + b • y) = Real.exp (f (a • x + b • y)) := (Real.exp_log (gpos _)).symm
      _ ≤ Real.exp (a • f x + b • f y) :=
          Real.exp_le_exp.mpr (fconv.2 trivial trivial ha hb hab)
      _ ≤ a • Real.exp (f x) + b • Real.exp (f y) := convexOn_exp.2 trivial trivial ha hb hab
      _ = a • g x + b • g y := by
          simp only [hf]
          rw [Real.exp_log (gpos x), Real.exp_log (gpos y)]
  have gmono := gconv.monotoneOn_deriv (fun x _ => (gd x).differentiableAt)
  intro x y hxy
  have := gmono trivial trivial hxy
  rw [(gd x).deriv, (gd y).deriv] at this
  linarith
