-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.logarithmicCenterIdeal_eq_or_comaximal
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T18:19:32.476997+00:00
-- url     : https://prove2.me/submissions/3dac5006-aeca-4884-a11f-8d6a0937f759

import Definitions.Def_OAI_PiExponent_LogarithmicCenterIdeals
import Mathlib

section

open OAI.PiExponent.FormalInterpolation

namespace PiL29

theorem eq_or_comax {m : Nat} (c₁ c₂ : Fin m → Complex)
    (T : Fin m → Nat) (e : Fin (m + 1) → Nat) :
    logarithmicCenterIdeal c₁ T e = logarithmicCenterIdeal c₂ T e ∨
      logarithmicCenterIdeal c₁ T e ⊔ logarithmicCenterIdeal c₂ T e = ⊤ := by
  by_cases h : c₁ = c₂
  · left; rw [h]
  · right
    obtain ⟨i, hi⟩ : ∃ i, c₁ i ≠ c₂ i := by
      by_contra hc; push_neg at hc; exact h (funext hc)
    set u : MvPolynomial (Fin (m + 1)) ℂ := MvPolynomial.X i.succ -
      Polynomial.aeval (MvPolynomial.X 0 - 1) (OAI.PiExponent.InterpolationMatrix.truncatedLog (T i))
    have hcop : IsCoprime (u - MvPolynomial.C (c₁ i)) (u - MvPolynomial.C (c₂ i)) := by
      have hne : c₂ i - c₁ i ≠ 0 := sub_ne_zero.2 (Ne.symm hi)
      refine ⟨MvPolynomial.C (c₂ i - c₁ i)⁻¹, -MvPolynomial.C (c₂ i - c₁ i)⁻¹, ?_⟩
      have : MvPolynomial.C (c₂ i - c₁ i)⁻¹ * MvPolynomial.C (c₂ i - c₁ i) = (1 : MvPolynomial (Fin (m + 1)) ℂ) := by
        rw [← map_mul, inv_mul_cancel₀ hne, map_one]
      rw [← this, map_sub]; ring
    have hcop' := hcop.pow (m := e i.succ) (n := e i.succ)
    obtain ⟨a, b, hab⟩ := hcop'
    have h1 : (u - MvPolynomial.C (c₁ i)) ^ e i.succ ∈ logarithmicCenterIdeal c₁ T e := by
      apply Ideal.subset_span
      refine ⟨i.succ, ?_⟩
      simp only [logarithmicCoordinate, Fin.cases_succ, u]; ring
    have h2 : (u - MvPolynomial.C (c₂ i)) ^ e i.succ ∈ logarithmicCenterIdeal c₂ T e := by
      apply Ideal.subset_span
      refine ⟨i.succ, ?_⟩
      simp only [logarithmicCoordinate, Fin.cases_succ, u]; ring
    rw [Ideal.eq_top_iff_one, ← hab]
    exact Ideal.add_mem _ (Ideal.mem_sup_left (Ideal.mul_mem_left _ _ h1))
      (Ideal.mem_sup_right (Ideal.mul_mem_left _ _ h2))

end PiL29

end

open OAI OAI.PiExponent OAI.PiExponent.FormalInterpolation

open OAI.PiExponent.FormalInterpolation

theorem solution
    {m : Nat} (c₁ c₂ : Fin m → Complex)
    (T : Fin m → Nat) (e : Fin (m + 1) → Nat) :
    logarithmicCenterIdeal c₁ T e = logarithmicCenterIdeal c₂ T e ∨
      logarithmicCenterIdeal c₁ T e ⊔ logarithmicCenterIdeal c₂ T e = ⊤ := by
  apply PiL29.eq_or_comax <;> assumption
