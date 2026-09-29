-- Prove2me | solution 1 for NeutrinoDecoherence.survival_probability_case1
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-26T07:59:51.045638+00:00
-- url     : https://prove2.me/submissions/4fc6b365-97b0-4080-b92d-73862b24baf3

import Mathlib
import Definitions.Def_NeutrinoDecoherence_Defs

set_option autoImplicit false

open scoped ComplexOrder

open NeutrinoDecoherence Matrix Complex in
theorem nd_lind1 (Δm2 E γ : ℝ) (ρ : Matrix (Fin 2) (Fin 2) ℂ) :
    lindbladian (twoFlavourHamiltonian Δm2 E) (Matrix.diagonal ![0, 0, (γ : ℂ)]) ρ =
      !![0, (-2 * γ + ((Δm2 / (2 * E) : ℝ) : ℂ) * I) * ρ 0 1;
         (-2 * γ - ((Δm2 / (2 * E) : ℝ) : ℂ) * I) * ρ 1 0, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [lindbladian, dissipator, twoFlavourHamiltonian, pauli, Fin.sum_univ_three,
      Matrix.mul_apply, Fin.sum_univ_two, Matrix.diagonal_apply, Matrix.vecMul, dotProduct] <;>
    ring_nf
  all_goals simp

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
theorem nd_case1 (θ α Δm2 E γ : ℝ) (hE : 0 < E) (hγ : 0 ≤ γ)
    (ρ : ℝ → Matrix (Fin 2) (Fin 2) ℂ)
    (hsol : IsLindbladSolution (twoFlavourHamiltonian Δm2 E)
      (Matrix.diagonal ![0, 0, (γ : ℂ)]) ρ)
    (h0 : ρ 0 = muonInitialState θ α) (L : ℝ) (hL : 0 ≤ L) :
    ρ L = !![((Real.cos θ ^ 2 : ℝ) : ℂ),
        exp (((-2 * γ * L : ℝ) : ℂ) + ((α + Δm2 / (2 * E) * L : ℝ) : ℂ) * I) *
          ((Real.cos θ * Real.sin θ : ℝ) : ℂ);
        exp (((-2 * γ * L : ℝ) : ℂ) - ((α + Δm2 / (2 * E) * L : ℝ) : ℂ) * I) *
          ((Real.cos θ * Real.sin θ : ℝ) : ℂ),
        ((Real.sin θ ^ 2 : ℝ) : ℂ)] := by
  have hd : ∀ (i j : Fin 2) (c : ℂ),
      (∀ t : ℝ, 0 ≤ t → lindbladian (twoFlavourHamiltonian Δm2 E)
        (Matrix.diagonal ![0, 0, (γ : ℂ)]) (ρ t) i j = c * ρ t i j) →
      ρ L i j = exp (c * (L : ℂ)) * ρ 0 i j := by
    intro i j c hc
    exact nd_ode (fun s => ρ s i j) c (fun t ht => by
      have := hsol t ht i j
      rwa [hc t ht] at this) L hL
  have h00 := hd 0 0 0 (fun t _ => by rw [nd_lind1]; simp)
  have h11 := hd 1 1 0 (fun t _ => by rw [nd_lind1]; simp)
  have h01 := hd 0 1 (-2 * γ + ((Δm2 / (2 * E) : ℝ) : ℂ) * I) (fun t _ => by rw [nd_lind1]; simp)
  have h10 := hd 1 0 (-2 * γ - ((Δm2 / (2 * E) : ℝ) : ℂ) * I) (fun t _ => by rw [nd_lind1]; simp)
  rw [h0, nd_muon] at h00 h11 h01 h10
  have e00 : ρ L 0 0 = ((Real.cos θ ^ 2 : ℝ) : ℂ) := by rw [h00]; simp
  have e11 : ρ L 1 1 = ((Real.sin θ ^ 2 : ℝ) : ℂ) := by rw [h11]; simp
  have e01 : ρ L 0 1 = exp (((-2 * γ * L : ℝ) : ℂ) + ((α + Δm2 / (2 * E) * L : ℝ) : ℂ) * I) *
          ((Real.cos θ * Real.sin θ : ℝ) : ℂ) := by
    rw [h01]
    simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one]
    rw [← mul_assoc, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  have e10 : ρ L 1 0 = exp (((-2 * γ * L : ℝ) : ℂ) - ((α + Δm2 / (2 * E) * L : ℝ) : ℂ) * I) *
          ((Real.cos θ * Real.sin θ : ℝ) : ℂ) := by
    rw [h10]
    simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one]
    rw [← mul_assoc, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  rw [Matrix.eta_fin_two (ρ L), e00, e01, e10, e11]

open NeutrinoDecoherence Matrix Complex in
theorem solution (θ α Δm2 E γ : ℝ) (hE : 0 < E) (hγ : 0 ≤ γ)
    (ρ : ℝ → Matrix (Fin 2) (Fin 2) ℂ)
    (hsol : IsLindbladSolution (twoFlavourHamiltonian Δm2 E)
      (Matrix.diagonal ![0, 0, (γ : ℂ)]) ρ)
    (h0 : ρ 0 = muonInitialState θ α) (L : ℝ) (hL : 0 ≤ L) :
    transitionProbability (ρ L) (muonInitialState θ α) =
      (3 + Real.cos (4 * θ) +
        2 * Real.exp (-2 * γ * L) * Real.cos (Δm2 / (2 * E) * L) *
          Real.sin (2 * θ) ^ 2) / 4 := by
  have key : exp (((-2 * γ * L : ℝ) : ℂ) + ((α + Δm2 / (2 * E) * L : ℝ) : ℂ) * I) *
        exp (-((α : ℂ) * I)) +
      exp (((-2 * γ * L : ℝ) : ℂ) - ((α + Δm2 / (2 * E) * L : ℝ) : ℂ) * I) * exp ((α : ℂ) * I) =
      ((2 * Real.exp (-2 * γ * L) * Real.cos (Δm2 / (2 * E) * L) : ℝ) : ℂ) := by
    rw [← Complex.exp_add, ← Complex.exp_add]
    have hx1 : ((-2 * γ * L : ℝ) : ℂ) + ((α + Δm2 / (2 * E) * L : ℝ) : ℂ) * I + -((α : ℂ) * I) =
        ((-2 * γ * L : ℝ) : ℂ) + ((Δm2 / (2 * E) * L : ℝ) : ℂ) * I := by push_cast; ring
    have hx2 : ((-2 * γ * L : ℝ) : ℂ) - ((α + Δm2 / (2 * E) * L : ℝ) : ℂ) * I + (α : ℂ) * I =
        ((-2 * γ * L : ℝ) : ℂ) + ((-(Δm2 / (2 * E) * L) : ℝ) : ℂ) * I := by push_cast; ring
    rw [hx1, hx2, Complex.exp_add, Complex.exp_add, Complex.exp_mul_I, Complex.exp_mul_I,
      ← Complex.ofReal_exp, ← Complex.ofReal_cos, ← Complex.ofReal_sin, ← Complex.ofReal_cos,
      ← Complex.ofReal_sin, Real.cos_neg, Real.sin_neg]
    push_cast
    ring
  have hc : (transitionProbability (ρ L) (muonInitialState θ α) : ℂ) =
      (((Real.cos θ ^ 4 + Real.sin θ ^ 4 +
        2 * Real.exp (-2 * γ * L) * Real.cos (Δm2 / (2 * E) * L) *
          (Real.cos θ ^ 2 * Real.sin θ ^ 2)) : ℝ) : ℂ) := by
    unfold transitionProbability
    rw [nd_case1 θ α Δm2 E γ hE hγ ρ hsol h0 L hL, nd_muon, Matrix.mul_fin_two,
      Matrix.trace_fin_two_of]
    have hre : (((Real.cos θ ^ 2 : ℝ) : ℂ) * ((Real.cos θ ^ 2 : ℝ) : ℂ) +
        exp (((-2 * γ * L : ℝ) : ℂ) + ((α + Δm2 / (2 * E) * L : ℝ) : ℂ) * I) *
          ((Real.cos θ * Real.sin θ : ℝ) : ℂ) *
          (exp (-((α : ℂ) * I)) * ((Real.cos θ * Real.sin θ : ℝ) : ℂ)) +
        (exp (((-2 * γ * L : ℝ) : ℂ) - ((α + Δm2 / (2 * E) * L : ℝ) : ℂ) * I) *
          ((Real.cos θ * Real.sin θ : ℝ) : ℂ) *
          (exp ((α : ℂ) * I) * ((Real.cos θ * Real.sin θ : ℝ) : ℂ)) +
          ((Real.sin θ ^ 2 : ℝ) : ℂ) * ((Real.sin θ ^ 2 : ℝ) : ℂ))) =
        (((Real.cos θ ^ 4 + Real.sin θ ^ 4 +
          2 * Real.exp (-2 * γ * L) * Real.cos (Δm2 / (2 * E) * L) *
            (Real.cos θ ^ 2 * Real.sin θ ^ 2)) : ℝ) : ℂ) := by
      linear_combination (norm := skip) (((Real.cos θ * Real.sin θ : ℝ) : ℂ)) ^ 2 * key
      push_cast
      ring
    rw [hre, Complex.ofReal_re]
  have hr : transitionProbability (ρ L) (muonInitialState θ α) =
      Real.cos θ ^ 4 + Real.sin θ ^ 4 +
        2 * Real.exp (-2 * γ * L) * Real.cos (Δm2 / (2 * E) * L) *
          (Real.cos θ ^ 2 * Real.sin θ ^ 2) := by exact_mod_cast hc
  rw [hr, show (4 : ℝ) * θ = 2 * (2 * θ) by ring, Real.cos_two_mul, Real.cos_two_mul,
    Real.sin_two_mul]
  linear_combination (Real.sin θ ^ 2 + 1 - Real.cos θ ^ 2) * (Real.sin_sq_add_cos_sq θ)
