-- Prove2me | solution 1 for NeutrinoDecoherence.case4_population
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-26T08:01:01.677129+00:00
-- url     : https://prove2.me/submissions/4bb858dc-8bf0-4f32-8196-b87a4457d5bf

import Mathlib
import Definitions.Def_NeutrinoDecoherence_Defs

set_option autoImplicit false

open scoped ComplexOrder

open Complex in
theorem nd_ode (f : ℝ → ℂ) (c : ℂ)
    (hf : ∀ t : ℝ, 0 ≤ t → HasDerivWithinAt f (c * f t) (Set.Ici 0) t) (L : ℝ) (hL : 0 ≤ L) :
    f L = exp (c * (L : ℂ)) * f 0 := by
  set g : ℝ → ℂ := fun t => exp (-(c * (t : ℂ))) * f t with hgdef
  have hg : ∀ t : ℝ, 0 ≤ t → HasDerivWithinAt g 0 (Set.Ici 0) t := by
    intro t ht
    have h1 : HasDerivAt (fun s : ℝ => exp (-(c * (s : ℂ)))) (exp (-(c * (t : ℂ))) * (-(c * 1))) t :=
      (((hasDerivAt_id t).ofReal_comp).const_mul c).neg.cexp
    have h2 : HasDerivWithinAt g (exp (-(c * (t : ℂ))) * (-(c * 1)) * f t +
        exp (-(c * (t : ℂ))) * (c * f t)) (Set.Ici 0) t := h1.hasDerivWithinAt.mul (hf t ht)
    exact h2.congr_deriv (by ring)
  have hcont : ContinuousOn g (Set.Icc 0 L) := fun x hx =>
    (hg x hx.1).continuousWithinAt.mono Set.Icc_subset_Ici_self
  have hconst := constant_of_has_deriv_right_zero hcont
    (fun x hx => (hg x hx.1).mono (Set.Ici_subset_Ici.mpr hx.1)) L ⟨hL, le_refl L⟩
  simp only [hgdef, Complex.ofReal_zero, mul_zero, neg_zero, Complex.exp_zero, one_mul] at hconst
  rw [← hconst, ← mul_assoc, ← Complex.exp_add]
  simp

open NeutrinoDecoherence Matrix Complex in
theorem nd_lind4 (Δm2 E γ : ℝ) (ρ : Matrix (Fin 2) (Fin 2) ℂ) :
    lindbladian (twoFlavourHamiltonian Δm2 E) (Matrix.diagonal ![0, (γ : ℂ), 0]) ρ 0 0 =
      γ * (ρ 1 1 - ρ 0 0) ∧
    lindbladian (twoFlavourHamiltonian Δm2 E) (Matrix.diagonal ![0, (γ : ℂ), 0]) ρ 1 1 =
      γ * (ρ 0 0 - ρ 1 1) := by
  constructor <;>
    simp [lindbladian, dissipator, twoFlavourHamiltonian, pauli, Fin.sum_univ_three,
      Matrix.mul_apply, Fin.sum_univ_two, Matrix.diagonal_apply, Matrix.vecMul, dotProduct] <;>
    ring_nf <;> simp only [Complex.I_sq] <;> ring

open NeutrinoDecoherence Matrix Complex in
theorem nd_muon (θ α : ℝ) :
    muonInitialState θ α = !![((Real.cos θ ^ 2 : ℝ) : ℂ),
        exp ((α : ℂ) * I) * ((Real.cos θ * Real.sin θ : ℝ) : ℂ);
        exp (-((α : ℂ) * I)) * ((Real.cos θ * Real.sin θ : ℝ) : ℂ),
        ((Real.sin θ ^ 2 : ℝ) : ℂ)] := by
  have hE : (starRingEnd ℂ) (exp ((α : ℂ) * I)) = exp (-((α : ℂ) * I)) := by
    rw [← Complex.exp_conj]; simp
  have hE1 : exp (-((α : ℂ) * I)) * exp ((α : ℂ) * I) = 1 := by
    rw [← Complex.exp_add]; simp
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [muonInitialState, mixingMatrix, Matrix.mul_apply, Fin.sum_univ_two, Matrix.single_apply,
      ← Complex.cos_conj, ← Complex.sin_conj, ← Complex.exp_conj] <;>
    first | linear_combination (Complex.sin (θ : ℂ)) ^ 2 * hE1 | ring

open NeutrinoDecoherence Matrix Complex in
theorem solution (θ α Δm2 E γ : ℝ) (hE : 0 < E) (hγ : 0 ≤ γ)
    (ρ : ℝ → Matrix (Fin 2) (Fin 2) ℂ)
    (hsol : IsLindbladSolution (twoFlavourHamiltonian Δm2 E)
      (Matrix.diagonal ![0, (γ : ℂ), 0]) ρ)
    (h0 : ρ 0 = muonInitialState θ α) (L : ℝ) (hL : 0 ≤ L) :
    ρ L 0 0 = (((1 + Real.exp (-2 * γ * L) * Real.cos (2 * θ)) / 2 : ℝ) : ℂ) := by
  have hp := nd_ode (fun s => ρ s 0 0 + ρ s 1 1) 0 (fun t ht => by
      have h := (hsol t ht 0 0).add (hsol t ht 1 1)
      obtain ⟨e1, e2⟩ := nd_lind4 Δm2 E γ (ρ t)
      rw [e1, e2] at h
      exact h.congr_deriv (by ring)) L hL
  have hq := nd_ode (fun s => ρ s 0 0 - ρ s 1 1) (-2 * (γ : ℂ)) (fun t ht => by
      have h := (hsol t ht 0 0).sub (hsol t ht 1 1)
      obtain ⟨e1, e2⟩ := nd_lind4 Δm2 E γ (ρ t)
      rw [e1, e2] at h
      exact h.congr_deriv (by ring)) L hL
  simp only [h0, nd_muon] at hp hq
  have hreal : (1 + Real.exp (-2 * γ * L) * Real.cos (2 * θ)) / 2 =
      ((Real.cos θ ^ 2 + Real.sin θ ^ 2) +
        Real.exp (-2 * γ * L) * (Real.cos θ ^ 2 - Real.sin θ ^ 2)) / 2 := by
    rw [Real.cos_two_mul]
    linear_combination (-(1 - Real.exp (-2 * γ * L)) / 2) * Real.sin_sq_add_cos_sq θ
  have hsplit : ρ L 0 0 = ((ρ L 0 0 + ρ L 1 1) + (ρ L 0 0 - ρ L 1 1)) / 2 := by ring
  rw [hreal, hsplit, hp, hq]
  simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one, zero_mul, Complex.exp_zero, one_mul]
  push_cast
  ring_nf
