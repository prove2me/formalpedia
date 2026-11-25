-- Prove2me | solution 1 for GlobalTheory.Published.Metaplectic.Model.shear_coeff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T18:09:20.834795+00:00
-- url     : https://prove2.me/submissions/39fe6641-fdb6-44f0-98c6-03e396067c99

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_MetaplecticRepresentation
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_HolPartShear

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix Complex
open scoped Real SchwartzMap ComplexConjugate
open GlobalTheory GlobalTheory.Published GlobalTheory.Published.Metaplectic GlobalTheory.Published.Metaplectic.Model
variable {ι : Type} [Fintype ι] [DecidableEq ι]
namespace GlobalTheory.Published.Metaplectic.Model
theorem _root_.solution (c : ℝ) :
    (∫ x : ℝ, cexp (-π * I * (c * x ^ 2)) * cexp (-π * x ^ 2) * conj (cexp (-π * x ^ 2))) ^ 2 * ((2 + I * c) / 2) =
      (∫ x : ℝ, cexp (-π * x ^ 2) * conj (cexp (-π * x ^ 2))) ^ 2 := by
  have hc : ∀ x : ℝ, conj (cexp (-π * x ^ 2)) = cexp (-π * x ^ 2) := by
    intro x; rw [← Complex.exp_conj]; simp
  have e1 : ∀ x : ℝ, cexp (-π * I * (c * x ^ 2)) * cexp (-π * x ^ 2) * conj (cexp (-π * x ^ 2)) =
      cexp (-(π * (2 + I * c)) * x ^ 2) := by
    intro x; rw [hc, ← Complex.exp_add, ← Complex.exp_add]; congr 1; ring
  have e2 : ∀ x : ℝ, cexp (-π * x ^ 2) * conj (cexp (-π * x ^ 2)) = cexp (-(π * 2) * x ^ 2) := by
    intro x; rw [hc, ← Complex.exp_add]; congr 1; ring
  simp_rw [e1, e2]
  have hp := Real.pi_pos
  rw [integral_gaussian_complex (by simp; positivity), integral_gaussian_complex (by simp; positivity)]
  have h2 : ∀ z : ℂ, (z ^ (1 / 2 : ℂ)) ^ 2 = z := fun z => by
    have := Complex.cpow_nat_inv_pow z (n := 2) two_ne_zero
    simpa using this
  rw [h2, h2]
  have h3 : (2 + I * c : ℂ) ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this
  have h4 : (π : ℂ) ≠ 0 := by exact_mod_cast hp.ne'
  field_simp
end GlobalTheory.Published.Metaplectic.Model
