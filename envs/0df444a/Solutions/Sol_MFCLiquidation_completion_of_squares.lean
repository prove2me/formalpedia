-- Prove2me | solution 1 for MFCLiquidation.completion_of_squares
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-12T01:02:48.21736+00:00
-- url     : https://prove2.me/submissions/7a1125e9-d354-4b8c-ab39-3708cff04e76

import Mathlib
import Definitions.Def_MFCLiquidation_Params
import Definitions.Def_MFCLiquidation_Riccati

open Matrix

open MFCLiquidation in
theorem solution (p : Params) (hp : p.Standing) (hγ : 0 < p.γ₂)
    (Ex0 sg a₁₁ a₁₃ a₃₃ b₁₁ b₁₃ b₃₃ d₁ d₃ : ℝ) :
    let A := p.symMat a₁₁ a₁₃ a₃₃
    let B := p.symMat b₁₁ b₁₃ b₃₃
    let Adot := p.symMatDot (p.rhsA₁₁ a₁₁) (p.rhsA₁₃ a₁₁ a₁₃) (p.rhsA₃₃ a₁₃ a₃₃)
    let Bdot := p.symMatDot (p.rhsB₁₁ b₁₁ b₁₃) (p.rhsB₁₃ b₁₁ b₁₃ b₃₃) (p.rhsB₃₃ b₁₃ b₃₃)
    let Dv := p.dVec d₁ d₃
    let Ddot := p.dVec (p.rhsD₁ Ex0 b₁₁ b₁₃ d₁ d₃) (p.rhsD₃ Ex0 b₁₃ b₃₃ d₁ d₃)
    let iA := p.IA a₁₁ a₁₃
    let iB := p.IB b₁₁ b₁₃ b₃₃
    let iD := p.ID Ex0 d₁ d₃
    (1 / p.aTilde) • Matrix.vecMulVec iA iA = p.Q + p.Hᵀ * A + A * p.H + Adot ∧
    (1 / p.a) • Matrix.vecMulVec iB iB = p.Q + Bdot + p.Hᵀ * B + B * p.H + p.Hbarᵀ * B + B * p.Hbar ∧
    (2 * iD / p.a) • iB = (2 : ℝ) • (p.G Ex0 ᵥ* B) + Ddot + Dv ᵥ* p.H + Dv ᵥ* p.Hbar ∧
    iD ^ 2 / p.a = ![0, sg, 0] ⬝ᵥ (A *ᵥ ![0, sg, 0]) + Dv ⬝ᵥ p.G Ex0
      - p.genF Ex0 sg a₁₁ d₁ d₃ := by
  intro A B Adot Bdot Dv Ddot iA iB iD
  obtain ⟨hγ1, _, hα, _, _, _, _, ha⟩ := hp
  have hγ' : p.γ₂ ≠ 0 := hγ.ne'
  have haT : p.γ₂ * p.ρ + p.lam ≠ 0 := by
    have := mul_nonneg hγ1 hα
    intro h; linarith
  have ha' : p.γ₂ * p.ρ - p.γ₁ * p.α + p.lam ≠ 0 := ha.ne'
  have ha'' : p.lam + p.γ₂ * p.ρ - p.α * p.γ₁ ≠ 0 := by
    intro h; apply ha'; linarith
  have hn : -(p.α * p.γ₁) + p.γ₂ * p.ρ + p.lam ≠ 0 := by
    intro h; apply ha'; linarith
  have hn2 : -(p.γ₁ * p.α) + p.γ₂ * p.ρ + p.lam ≠ 0 := by
    intro h; apply ha'; linarith
  have hX : (-(p.α * p.γ₁) + p.γ₂ * p.ρ + p.lam) * (-(p.α * p.γ₁) + p.γ₂ * p.ρ + p.lam)⁻¹ = 1 :=
    mul_inv_cancel₀ hn
  refine ⟨?_, ?_, ?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [A, Adot, iA, Params.symMat, Params.symMatDot, Params.IA, Params.aTilde, Params.Q,
        Params.H, Params.rhsA₁₁, Params.rhsA₁₃, Params.rhsA₃₃, Matrix.mul_apply,
        Fin.sum_univ_three, Matrix.vecMulVec_apply] <;>
      field_simp <;> ring
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [B, Bdot, iB, Params.symMat, Params.symMatDot, Params.IB, Params.a, Params.Q,
        Params.H, Params.Hbar, Params.rhsB₁₁, Params.rhsB₁₃, Params.rhsB₃₃, Params.bX₁,
        Params.bX₃, Matrix.mul_apply, Fin.sum_univ_three, Matrix.vecMulVec_apply] <;>
      field_simp <;> ring
  · funext j
    fin_cases j <;>
      simp [B, Dv, Ddot, iB, iD, Params.symMat, Params.dVec, Params.IB, Params.ID, Params.a,
        Params.G, Params.H, Params.Hbar, Params.rhsD₁, Params.rhsD₃, Params.bX₁, Params.bX₃,
        Params.dY, Matrix.vecMul, dotProduct, Fin.sum_univ_three] <;>
      field_simp <;>
      first
        | ring1
        | linear_combination (2*p.γ₂*(-Ex0*p.α*p.γ₁*p.γ₂ + p.α*d₁*p.γ₁ + p.α*d₃*p.γ₂ - d₁*p.γ₂*p.ρ)) * hX
  · simp [A, Dv, iD, Params.symMat, Params.dVec, Params.ID, Params.a, Params.G, Params.genF,
      Matrix.mulVec, dotProduct, Fin.sum_univ_three] <;>
    field_simp <;>
    first
      | ring1
      | linear_combination (4*(-Ex0*p.α*p.γ₁*p.γ₂ + p.α*d₁*p.γ₁ + p.α*d₃*p.γ₂ - d₁*p.γ₂*p.ρ)^2) * hX
