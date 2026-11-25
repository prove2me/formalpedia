-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.ExplChi.logDeriv_LFunction_functional_equation
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T02:29:51.305429+00:00
-- url     : https://prove2.me/submissions/65d5929d-32c8-4936-bab5-2efa632e264c

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_DirichletLogDerivReflectionFormula
import Theorems.Thm_GlobalTheory_CompanionTheory_ExplChi_completed_logDeriv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.ExplChi
open Complex DirichletCharacter
namespace GlobalTheory.CompanionTheory.ExplChi
theorem _root_.solution :
    ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), 1 < N → χ.IsPrimitive →
      ∀ a : ℂ, (χ.Even ∧ a = 0 ∨ χ.Odd ∧ a = 1) → ∀ s : ℂ,
        (∀ n : ℕ, (s + a) / 2 ≠ -(n : ℂ)) → (∀ n : ℕ, (1 - s + a) / 2 ≠ -(n : ℂ)) →
        DirichletCharacter.LFunction χ s ≠ 0 →
        DirichletCharacter.LFunction χ⁻¹ (1 - s) ≠ 0 →
        deriv (DirichletCharacter.LFunction χ) s / DirichletCharacter.LFunction χ s =
          -((Real.log (N / Real.pi) : ℝ) : ℂ) - Complex.digamma ((1 - s + a) / 2) / 2 -
            Complex.digamma ((s + a) / 2) / 2 -
            deriv (DirichletCharacter.LFunction χ⁻¹) (1 - s) /
              DirichletCharacter.LFunction χ⁻¹ (1 - s) := by
  intro N _ χ hN hp a ha s hs1 hs2 hL1 hL2
  have hN1 : N ≠ 1 := hN.ne'
  have hχ : χ ≠ 1 := by
    rintro rfl
    rw [isPrimitive_def, conductor_one] at hp
    exact hN1 hp.symm
  have hχi : χ⁻¹ ≠ 1 := inv_ne_one.mpr hχ
  have ha' : χ⁻¹.Even ∧ a = 0 ∨ χ⁻¹.Odd ∧ a = 1 := by
    rcases ha with ⟨he, h⟩ | ⟨ho, h⟩
    · refine Or.inl ⟨?_, h⟩
      rw [DirichletCharacter.Even, MulChar.inv_apply_eq_inv', he, inv_one]
    · refine Or.inr ⟨?_, h⟩
      rw [DirichletCharacter.Odd, MulChar.inv_apply_eq_inv', ho]
      norm_num
  obtain ⟨A0, eA⟩ := completed_logDeriv χ hN1 hχ ha hs1 hL1
  obtain ⟨B0, eB⟩ := completed_logDeriv χ⁻¹ hN1 hχi ha' hs2 hL2
  have hN0 : (N : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne N
  set W := rootNumber χ with hW
  have hfe : ∀ w, completedLFunction χ w =
      (N : ℂ) ^ ((1 : ℂ) / 2 - w) * W * completedLFunction χ⁻¹ (1 - w) := by
    intro w
    have h := hp.completedLFunction_one_sub (1 - w)
    rw [sub_sub_cancel] at h
    rw [h]
    congr 3
    ring
  have hc : HasDerivAt (fun w : ℂ => (N : ℂ) ^ ((1 : ℂ) / 2 - w))
      ((N : ℂ) ^ ((1 : ℂ) / 2 - s) * Complex.log N * (-1)) s :=
    ((hasDerivAt_id s).const_sub ((1 : ℂ) / 2)).const_cpow (Or.inl hN0)
  have hB : HasDerivAt (fun w : ℂ => completedLFunction χ⁻¹ (1 - w))
      (-deriv (completedLFunction χ⁻¹) (1 - s)) s :=
    ((differentiable_completedLFunction hχi (1 - s)).hasDerivAt).comp_const_sub 1 s
  have hT := (hc.mul_const W).mul hB
  have hD : deriv (completedLFunction χ) s =
      (N : ℂ) ^ ((1 : ℂ) / 2 - s) * Complex.log N * (-1) * W * completedLFunction χ⁻¹ (1 - s) +
        (N : ℂ) ^ ((1 : ℂ) / 2 - s) * W * (-deriv (completedLFunction χ⁻¹) (1 - s)) := by
    rw [funext hfe]
    exact hT.deriv
  have hA : completedLFunction χ s =
      (N : ℂ) ^ ((1 : ℂ) / 2 - s) * W * completedLFunction χ⁻¹ (1 - s) := hfe s
  have hcW : (N : ℂ) ^ ((1 : ℂ) / 2 - s) * W ≠ 0 := by
    intro h
    rw [h, zero_mul] at hA
    exact A0 hA
  have hlog : deriv (completedLFunction χ) s / completedLFunction χ s =
      -Complex.log N -
        deriv (completedLFunction χ⁻¹) (1 - s) / completedLFunction χ⁻¹ (1 - s) := by
    have hBB : completedLFunction χ⁻¹ (1 - s) *
        (deriv (completedLFunction χ⁻¹) (1 - s) / completedLFunction χ⁻¹ (1 - s)) =
        deriv (completedLFunction χ⁻¹) (1 - s) := mul_div_cancel₀ _ B0
    rw [hD, hA, div_eq_iff (mul_ne_zero hcW B0)]
    linear_combination ((N : ℂ) ^ ((1 : ℂ) / 2 - s) * W) * hBB
  have hNpos : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  have l1 : ((Real.log (N / Real.pi) : ℝ) : ℂ) = Complex.log N - (Real.log Real.pi : ℂ) := by
    rw [Real.log_div hNpos.ne' Real.pi_ne_zero, ofReal_sub, Complex.ofReal_log hNpos.le,
      ofReal_natCast]
  rw [eA, eB] at hlog
  rw [l1]
  linear_combination hlog
end GlobalTheory.CompanionTheory.ExplChi
