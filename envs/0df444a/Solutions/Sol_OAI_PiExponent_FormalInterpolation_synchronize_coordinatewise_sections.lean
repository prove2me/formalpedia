-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.synchronize_coordinatewise_sections
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T19:44:05.710575+00:00
-- url     : https://prove2.me/submissions/26dc5d81-abba-4a0e-8752-d06733a0b77a

import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_finite_power_generators

open scoped BigOperators

theorem solution
    {d : Nat} (I : Ideal (MvPolynomial (Fin d) Complex))
    (w : Fin d → Rat) (rho : Rat) (eps : Real)
    (hcoord : ∀ i : Fin d, ∃ s : Nat, ∃ n : Nat,
      ∃ F : Finset (MvPolynomial (Fin d) Complex),
        0 < s ∧ 0 < n ∧
        (∀ f ∈ F, f ∈ I ^ s) ∧
        MvPolynomial.X i ^ n ∈ Ideal.span (F : Set (MvPolynomial (Fin d) Complex)) ∧
        (n : Real) * (w i : Real) < (s : Real) * ((rho : Real) + eps)) :
    ∃ (s : Nat) (S : Finset (MvPolynomial (Fin d) Complex)),
      0 < s ∧
      (∀ f ∈ S, f ∈ I ^ s) ∧
      ∀ i : Fin d, ∃ n : Nat, 0 < n ∧
        MvPolynomial.X i ^ n ∈ Ideal.span (S : Set (MvPolynomial (Fin d) Complex)) ∧
        (n : Real) * (w i : Real) < (s : Real) * ((rho : Real) + eps) := by
  classical
  choose s₀ n₀ F₀ hs₀ hn₀ hF₀ hpow₀ hbound using hcoord
  obtain ⟨s, S, hs, hS, hsync⟩ :=
    OAI.PiExponent.FormalInterpolation.finite_power_generators
      I (fun i : Fin d => MvPolynomial.X i) s₀ n₀ F₀ hs₀ hn₀ hF₀ hpow₀
  refine ⟨s, S, hs, hS, ?_⟩
  intro i
  obtain ⟨k, hk, hsEq, hpow⟩ := hsync i
  refine ⟨n₀ i * k, Nat.mul_pos (hn₀ i) hk, hpow, ?_⟩
  have hkR : (0 : Real) < (k : Real) := by exact Nat.cast_pos.mpr hk
  have hscaled := mul_lt_mul_of_pos_right (hbound i) hkR
  calc
    ((n₀ i * k : Nat) : Real) * (w i : Real)
        = (((n₀ i : Real) * (w i : Real)) * (k : Real)) := by
            simp only [Nat.cast_mul]
            calc
              ((n₀ i : Real) * (k : Real)) * (w i : Real)
                  = (n₀ i : Real) * ((k : Real) * (w i : Real)) := by rw [mul_assoc]
              _ = (n₀ i : Real) * ((w i : Real) * (k : Real)) := by
                    rw [mul_comm (k : Real) (w i : Real)]
              _ = ((n₀ i : Real) * (w i : Real)) * (k : Real) := by
                    rw [← mul_assoc]
    _ < (((s₀ i : Real) * ((rho : Real) + eps)) * (k : Real)) := hscaled
    _ = (s : Real) * ((rho : Real) + eps) := by
            rw [hsEq, Nat.cast_mul]
            calc
              ((s₀ i : Real) * ((rho : Real) + eps)) * (k : Real)
                  = (s₀ i : Real) * (((rho : Real) + eps) * (k : Real)) := by
                      rw [mul_assoc]
              _ = (s₀ i : Real) * ((k : Real) * ((rho : Real) + eps)) := by
                    rw [mul_comm ((rho : Real) + eps) (k : Real)]
              _ = ((s₀ i : Real) * (k : Real)) * ((rho : Real) + eps) := by
                    rw [← mul_assoc]
