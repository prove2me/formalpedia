-- Prove2me | solution 1 for NeutrinoDecoherence.energy_conservation_iff
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-26T08:30:58.604052+00:00
-- url     : https://prove2.me/submissions/6a69916b-119c-4eb0-8253-37037150551b

import Mathlib
import Definitions.Def_NeutrinoDecoherence_Defs

set_option autoImplicit false

open scoped ComplexOrder

open NeutrinoDecoherence Matrix Complex in
theorem nd_tr (Δm2 E : ℝ) (a : Matrix (Fin 3) (Fin 3) ℂ) (ρ : Matrix (Fin 2) (Fin 2) ℂ) :
    (twoFlavourHamiltonian Δm2 E * lindbladian (twoFlavourHamiltonian Δm2 E) a ρ).trace =
      ((Δm2 / (2 * E) : ℝ) : ℂ) * dissipator a ρ 1 1 := by
  simp only [Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two, twoFlavourHamiltonian,
    lindbladian, Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply, Matrix.of_apply,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
    Matrix.cons_val_fin_one, smul_eq_mul]
  ring

open NeutrinoDecoherence Matrix Complex in
theorem nd_d1 (a : Matrix (Fin 3) (Fin 3) ℂ) :
    dissipator a !![1, 0; 0, 0] 1 1 = a 0 0 + a 1 1 - I * a 0 1 + I * a 1 0 := by
  simp [dissipator, pauli, Fin.sum_univ_three]
  ring_nf

open NeutrinoDecoherence Matrix Complex in
theorem nd_d2 (a : Matrix (Fin 3) (Fin 3) ℂ) :
    dissipator a !![0, 0; 0, 1] 1 1 = -(a 0 0 + a 1 1) - I * a 0 1 + I * a 1 0 := by
  simp [dissipator, pauli, Fin.sum_univ_three]
  ring_nf

open NeutrinoDecoherence Matrix Complex in
theorem nd_minor (a : Matrix (Fin 3) (Fin 3) ℂ) (ha : a.PosSemidef) (i j : Fin 3)
    (hi : a i i = 0) : a i j = 0 := by
  have h := (ha.submatrix ![i, j]).det_nonneg
  rw [Matrix.det_fin_two] at h
  simp [hi] at h
  have hh : a j i = star (a i j) := (ha.1.apply j i).symm
  rw [hh, Complex.star_def, Complex.mul_conj] at h
  have h2 : Complex.normSq (a i j) ≤ 0 := by exact_mod_cast h
  have h3 : Complex.normSq (a i j) = 0 := le_antisymm h2 (Complex.normSq_nonneg _)
  exact Complex.normSq_eq_zero.mp h3

open NeutrinoDecoherence Matrix Complex in
theorem nd_dens1 : IsDensityMatrix (!![1, 0; 0, 0] : Matrix (Fin 2) (Fin 2) ℂ) := by
  refine ⟨?_, ?_⟩
  · have := Matrix.posSemidef_vecMulVec_self_star (![1, 0] : Fin 2 → ℂ)
    convert this using 1
    ext i j; fin_cases i <;> fin_cases j <;> simp [vecMulVec]
  · simp [Matrix.trace_fin_two]

open NeutrinoDecoherence Matrix Complex in
theorem nd_dens2 : IsDensityMatrix (!![0, 0; 0, 1] : Matrix (Fin 2) (Fin 2) ℂ) := by
  refine ⟨?_, ?_⟩
  · have := Matrix.posSemidef_vecMulVec_self_star (![0, 1] : Fin 2 → ℂ)
    convert this using 1
    ext i j; fin_cases i <;> fin_cases j <;> simp [vecMulVec]
  · simp [Matrix.trace_fin_two]

open NeutrinoDecoherence Matrix Complex in
theorem nd_d3 (γ : ℝ) (ρ : Matrix (Fin 2) (Fin 2) ℂ) :
    dissipator (Matrix.diagonal ![0, 0, (γ : ℂ)]) ρ 1 1 = 0 := by
  simp [dissipator, pauli, Fin.sum_univ_three, Matrix.diagonal_apply, Matrix.mul_apply,
    Fin.sum_univ_two, Matrix.vecMul, dotProduct]
  ring_nf
  all_goals simp

open NeutrinoDecoherence Matrix Complex ComplexOrder in
theorem solution (Δm2 E : ℝ) (hE : 0 < E) (hΔ : Δm2 ≠ 0)
    (a : Matrix (Fin 3) (Fin 3) ℂ) (ha : a.PosSemidef) :
    (∀ ρ : Matrix (Fin 2) (Fin 2) ℂ, IsDensityMatrix ρ →
        (twoFlavourHamiltonian Δm2 E *
          lindbladian (twoFlavourHamiltonian Δm2 E) a ρ).trace = 0) ↔
      ∃ γ : ℝ, a = Matrix.diagonal ![0, 0, (γ : ℂ)] := by
  have hω : ((Δm2 / (2 * E) : ℝ) : ℂ) ≠ 0 := by
    have : Δm2 / (2 * E) ≠ 0 := div_ne_zero hΔ (by positivity)
    exact_mod_cast this
  constructor
  · intro h
    have h1 := h _ nd_dens1
    have h2 := h _ nd_dens2
    rw [nd_tr, nd_d1] at h1
    rw [nd_tr, nd_d2] at h2
    have h1' := (mul_eq_zero.mp h1).resolve_left hω
    have h2' := (mul_eq_zero.mp h2).resolve_left hω
    have hsum : a 0 0 + a 1 1 = 0 := by linear_combination (h1' - h2') / 2
    have d0 := ha.diag_nonneg (i := 0)
    have d1 := ha.diag_nonneg (i := 1)
    have d2 := ha.diag_nonneg (i := 2)
    rw [Complex.nonneg_iff] at d0 d1 d2
    have hre : (a 0 0).re + (a 1 1).re = 0 := by
      have := congrArg Complex.re hsum
      simpa using this
    have h00 : a 0 0 = 0 := Complex.ext (by simp; linarith [d0.1, d1.1]) (by simp; linarith [d0.2])
    have h11 : a 1 1 = 0 := Complex.ext (by simp; linarith [d0.1, d1.1]) (by simp; linarith [d1.2])
    have h22 : a 2 2 = (((a 2 2).re : ℝ) : ℂ) := Complex.ext (by simp) (by simp; linarith [d2.2])
    have h01 := nd_minor a ha 0 1 h00
    have h02 := nd_minor a ha 0 2 h00
    have h10 := nd_minor a ha 1 0 h11
    have h12 := nd_minor a ha 1 2 h11
    have h20 : a 2 0 = 0 := by
      have := ha.1.apply 2 0
      rw [h02, star_zero] at this
      exact this.symm
    have h21 : a 2 1 = 0 := by
      have := ha.1.apply 2 1
      rw [h12, star_zero] at this
      exact this.symm
    refine ⟨(a 2 2).re, ?_⟩
    ext i j
    fin_cases i <;> fin_cases j
    all_goals simp [h00, h01, h02, h10, h11, h12, h20, h21]
    exact h22
  · rintro ⟨γ, rfl⟩ ρ _
    rw [nd_tr, nd_d3, mul_zero]
