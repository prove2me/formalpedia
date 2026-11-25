-- Prove2me | solution 1 for GlobalTheory.LaurentFJ.coeff_eq_zero_of_hasSum_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:06:02.539063+00:00
-- url     : https://prove2.me/submissions/bd55da82-167c-4863-9cc9-9968380cf556

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FlowDomainCriterionHolds
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_M3bExpHolds
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_MajPos
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_CoeffEqZeroOfHasSumZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.LaurentFJ
open Complex ReciprocityTheory.ChartRestriction.G.FD
noncomputable section
namespace GlobalTheory.LaurentFJ
theorem _root_.solution (d : ℤ → ℂ)
    (h : ∀ t : ℝ, HasSum (fun k : ℤ => d k * cexp (2 * Real.pi * I * t) ^ k) 0) (j : ℤ) :
    d j = 0 := by
  have hs : Summable fun k => ‖d k‖ := by
    have := (h 0).summable
    simp only [ofReal_zero, mul_zero, Complex.exp_zero, one_zpow, mul_one] at this
    exact summable_norm_iff.mpr this
  have hpow : ∀ (k : ℤ) (t : ℝ), cexp (2 * Real.pi * I * t) ^ k * cexp (2 * Real.pi * I * t) ^ (-j)
      = cexp ((2 * Real.pi * I * ((k - j : ℤ) : ℂ)) * t) := by
    intro k t
    rw [← Complex.exp_int_mul, ← Complex.exp_int_mul, ← Complex.exp_add]
    congr 1; push_cast; ring
  have hI := intervalIntegral.hasSum_integral_of_dominated_convergence (μ := MeasureTheory.volume)
    (a := 0) (b := 1) (f := fun _ : ℝ => (0 : ℂ))
    (F := fun (k : ℤ) (t : ℝ) => d k * cexp ((2 * Real.pi * I * ((k - j : ℤ) : ℂ)) * t))
    (fun k _ => ‖d k‖)
    (fun k => (by fun_prop : Continuous fun t : ℝ =>
      d k * cexp ((2 * Real.pi * I * ((k - j : ℤ) : ℂ)) * t)).aestronglyMeasurable)
    (fun k => MeasureTheory.ae_of_all _ fun t _ => by
      have : (2 * Real.pi * I * ((k - j : ℤ) : ℂ)) * t =
          ((2 * Real.pi * ((k - j : ℤ) : ℝ) * t : ℝ) : ℂ) * I := by push_cast; ring
      rw [norm_mul, this, Complex.norm_exp_ofReal_mul_I, mul_one])
    (MeasureTheory.ae_of_all _ fun t _ => hs) intervalIntegrable_const
    (MeasureTheory.ae_of_all _ fun t _ => by
      have := (h t).mul_right (cexp (2 * Real.pi * I * t) ^ (-j))
      simp only [zero_mul, mul_assoc (d _), hpow] at this
      exact this)
  have hval : ∀ k : ℤ, (∫ t in (0 : ℝ)..1,
      d k * cexp ((2 * Real.pi * I * ((k - j : ℤ) : ℂ)) * t)) = if k = j then d j else 0 := by
    intro k
    split_ifs with hk
    · subst hk; simp
    · have hc : (2 * Real.pi * I * ((k - j : ℤ) : ℂ)) ≠ 0 := by
        refine mul_ne_zero Complex.two_pi_I_ne_zero ?_
        exact_mod_cast sub_ne_zero.mpr hk
      rw [intervalIntegral.integral_const_mul, integral_exp_mul_complex hc]
      have : cexp (2 * Real.pi * I * ((k - j : ℤ) : ℂ)) = 1 := by
        rw [mul_comm]; exact Complex.exp_int_mul_two_pi_mul_I _
      simp only [ofReal_one, mul_one, ofReal_zero, mul_zero, Complex.exp_zero, this]
      simp
  simp only [hval, intervalIntegral.integral_zero] at hI
  exact (hasSum_ite_eq j (d j)).unique hI
end GlobalTheory.LaurentFJ
