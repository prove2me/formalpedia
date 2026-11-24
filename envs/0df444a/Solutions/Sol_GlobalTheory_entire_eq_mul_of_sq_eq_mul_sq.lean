-- Prove2me | solution 1 for GlobalTheory.entire_eq_mul_of_sq_eq_mul_sq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:37:11.762745+00:00
-- url     : https://prove2.me/submissions/3527ac1b-bbe2-43e0-94f1-ca18c2fe09fd

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_EntireEqZeroOrEqZeroOfMulEqZero
import Theorems.Thm_GlobalTheory_entire_eq_zero_or_eq_zero_of_mul_eq_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
    ∀ (g : ℕ) (f h q : (Fin g → ℂ) → ℂ) (C : ℂ), Differentiable ℂ f → Differentiable ℂ h →
      Differentiable ℂ q → (∀ z, f z ^ 2 = C * Complex.exp (2 * q z) * h z ^ 2) →
      ∃ c : ℂ, c ^ 2 = C ∧ ∀ z, f z = c * Complex.exp (q z) * h z := by
  intro g f h q C hf hh hq hsq
  obtain ⟨c, hc⟩ := IsAlgClosed.exists_pow_nat_eq C (by norm_num : 0 < 2)
  have hF : Differentiable ℂ fun z => f z * Complex.exp (-q z) := hf.mul hq.neg.cexp
  have key : ∀ z, (f z * Complex.exp (-q z) - c * h z) * (f z * Complex.exp (-q z) + c * h z) = 0 := by
    intro z
    have e1 : Complex.exp (-q z) ^ 2 * Complex.exp (2 * q z) = 1 := by
      rw [← Complex.exp_nat_mul, ← Complex.exp_add]
      convert Complex.exp_zero using 2
      push_cast
      ring
    linear_combination Complex.exp (-q z) ^ 2 * hsq z + C * h z ^ 2 * e1 - h z ^ 2 * hc
  have e2 : ∀ z, Complex.exp (-q z) * Complex.exp (q z) = 1 := by
    intro z
    rw [← Complex.exp_add]
    simp
  rcases entire_eq_zero_or_eq_zero_of_mul_eq_zero (fun z => f z * Complex.exp (-q z) - c * h z)
      (fun z => f z * Complex.exp (-q z) + c * h z) (hF.sub ((differentiable_const c).mul hh))
      (hF.add ((differentiable_const c).mul hh)) key with h1 | h1
  · refine ⟨c, hc, fun z => ?_⟩
    linear_combination Complex.exp (q z) * h1 z - f z * e2 z
  · refine ⟨-c, by rw [neg_sq]; exact hc, fun z => ?_⟩
    linear_combination Complex.exp (q z) * h1 z - f z * e2 z
end GlobalTheory
