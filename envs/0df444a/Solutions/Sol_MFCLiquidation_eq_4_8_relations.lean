-- Prove2me | solution 1 for MFCLiquidation.eq_4_8_relations
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T17:47:32.036562+00:00
-- url     : https://prove2.me/submissions/8985d4da-5e50-4d80-95b5-dc2173eb5493

import Mathlib
import Definitions.Def_MFCLiquidation_Params
import Definitions.Def_MFCLiquidation_Riccati

open Matrix

open MFCLiquidation in
theorem solution (p : Params) (hγ : 0 < p.γ₂)
    (x₁₁ x₁₃ x₃₃ d₁ d₃ a₁₁ a₁₃ b₁₁ b₁₃ b₃₃ : ℝ) :
    p.K ᵥ* p.symMat x₁₁ x₁₃ x₃₃ = ![0, -(1 / 2), 0] ∧
    p.dVec d₁ d₃ ⬝ᵥ p.K = 0 ∧
    p.IA a₁₁ a₁₃ ⬝ᵥ p.K = p.aTilde ∧
    p.IB b₁₁ b₁₃ b₃₃ ⬝ᵥ p.K = p.a := by
  have hne : p.γ₂ ≠ 0 := hγ.ne'
  refine ⟨?_, ?_, ?_, ?_⟩
  · ext j
    fin_cases j <;>
      simp [vecMul, dotProduct, Fin.sum_univ_three, Params.K, Params.symMat] <;>
      field_simp <;> ring
  · simp [dotProduct, Fin.sum_univ_three, Params.K, Params.dVec] <;> field_simp <;> ring
  · simp [dotProduct, Fin.sum_univ_three, Params.K, Params.IA, Params.aTilde] <;>
      field_simp <;> ring
  · simp [dotProduct, Fin.sum_univ_three, Params.K, Params.IB, Params.a] <;>
      field_simp <;> ring
