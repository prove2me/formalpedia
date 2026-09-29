-- Prove2me | solution 1 for NeutrinoDecoherence.linearEntropy_bounds
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-26T08:16:02.412183+00:00
-- url     : https://prove2.me/submissions/654e15cc-bb84-44de-8b8d-0a998a2d62f1

import Mathlib
import Definitions.Def_NeutrinoDecoherence_Defs

set_option autoImplicit false

open scoped ComplexOrder

open Matrix in
theorem nd_trace_cfc {n : Type*} [Fintype n] [DecidableEq n] (A : Matrix n n ℂ)
    (hA : A.IsHermitian) (f : ℝ → ℝ) :
    (cfc f A).trace = ∑ i, ((f (hA.eigenvalues i) : ℝ) : ℂ) := by
  rw [hA.cfc_eq f, Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply, trace_mul_cycle,
    Unitary.coe_star_mul_self, one_mul, trace_diagonal]
  simp

open NeutrinoDecoherence Matrix in
theorem solution {n : Type*} [Fintype n] (ρ : Matrix n n ℂ)
    (hρ : IsDensityMatrix ρ) :
    0 ≤ linearEntropy ρ ∧ linearEntropy ρ ≤ 1 ∧ (linearEntropy ρ = 0 ↔ ρ * ρ = ρ) := by
  classical
  obtain ⟨hpsd, htr⟩ := hρ
  have hH : ρ.IsHermitian := hpsd.1
  have hsa : IsSelfAdjoint ρ := hH.isSelfAdjoint
  have hnn : ∀ i, 0 ≤ hH.eigenvalues i := hpsd.eigenvalues_nonneg
  have hsum : ∑ i, hH.eigenvalues i = 1 := by
    have h := hH.trace_eq_sum_eigenvalues
    rw [htr] at h
    have h2 := congrArg Complex.re h
    simp only [Complex.one_re, Complex.re_sum, Complex.ofReal_re] at h2
    exact h2.symm
  have hsq : cfc (fun x : ℝ => x * x) ρ = ρ * ρ := by
    rw [cfc_mul (fun x : ℝ => x) (fun x : ℝ => x) ρ, cfc_id' (R := ℝ) (a := ρ)]
  have hid : cfc (fun x : ℝ => x) ρ = ρ := cfc_id' (R := ℝ) (a := ρ)
  have htr2 : (ρ * ρ).trace.re = ∑ i, hH.eigenvalues i * hH.eigenvalues i := by
    rw [← hsq, nd_trace_cfc ρ hH]
    simp only [Complex.re_sum, Complex.ofReal_re]
  have hle1 : ∀ i, hH.eigenvalues i ≤ 1 := fun i =>
    hsum ▸ Finset.single_le_sum (fun j _ => hnn j) (Finset.mem_univ i)
  have hterm : ∀ i, 0 ≤ hH.eigenvalues i - hH.eigenvalues i * hH.eigenvalues i :=
    fun i => by nlinarith [hnn i, hle1 i]
  have hS : linearEntropy ρ = ∑ i, (hH.eigenvalues i - hH.eigenvalues i * hH.eigenvalues i) := by
    unfold linearEntropy
    rw [htr2, Finset.sum_sub_distrib, hsum]
  refine ⟨?_, ?_, ?_⟩
  · rw [hS]
    exact Finset.sum_nonneg (fun i _ => hterm i)
  · unfold linearEntropy
    rw [htr2]
    have := Finset.sum_nonneg (fun i (_ : i ∈ Finset.univ) => mul_self_nonneg (hH.eigenvalues i))
    linarith
  · rw [hS, Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hterm i)]
    constructor
    · intro h
      rw [← hsq]
      conv_rhs => rw [← hid]
      apply cfc_congr
      rw [hH.spectrum_real_eq_range_eigenvalues]
      rintro _ ⟨i, rfl⟩
      have := h i (Finset.mem_univ _)
      simp only
      linarith
    · intro h i _
      rw [← hsq] at h
      conv_rhs at h => rw [← hid]
      have h2 := eqOn_of_cfc_eq_cfc h
      rw [hH.spectrum_real_eq_range_eigenvalues] at h2
      have h3 := h2 ⟨i, rfl⟩
      simp only at h3
      linarith
