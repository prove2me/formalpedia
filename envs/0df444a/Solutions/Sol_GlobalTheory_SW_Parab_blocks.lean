-- Prove2me | solution 1 for GlobalTheory.SW.Parab.blocks
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:48:10.403942+00:00
-- url     : https://prove2.me/submissions/02c37242-a875-4041-bd99-a3c7b7c4d4f3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ThHEqThSDictionary
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_UnitaryActHalfSpace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_QuadCocycle
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_HermitianWeilActionUnitaryGroupTestFunctionsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_HermitianWeilActionSiegelParabolicExplicit
import Theorems.Thm_GlobalTheory_SW_Base_ccT_ccT
import Theorems.Thm_GlobalTheory_SW_Base_ccT_mul
import Theorems.Thm_GlobalTheory_SW_HAct_ccT_ccT
import Theorems.Thm_GlobalTheory_SW_HAct_ccT_mul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.Parab
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Ψ : Finset (E →+* ℂ)} {n N : ℕ}
namespace GlobalTheory.SW.Parab
theorem _root_.solution {γ : M2 E N} (hγ : γ ∈ UU E N) (h0 : γ.toBlocks₂₁ = 0) :
    ccT γ.toBlocks₁₁ * γ.toBlocks₂₂ = 1 ∧
      ccT (γ.toBlocks₁₂ * ccT γ.toBlocks₁₁) = γ.toBlocks₁₂ * ccT γ.toBlocks₁₁ := by
  have h : ccT γ * Matrix.J (Fin N) E * γ = Matrix.J (Fin N) E := hγ
  have e : ccT γ = Matrix.fromBlocks (ccT γ.toBlocks₁₁) (ccT γ.toBlocks₂₁) (ccT γ.toBlocks₁₂)
      (ccT γ.toBlocks₂₂) := by
    ext (i | i) (j | j) <;> rfl
  rw [e] at h
  nth_rewrite 5 [← Matrix.fromBlocks_toBlocks γ] at h
  have z : ccT (0 : Matrix (Fin N) (Fin N) E) = 0 := by ext i j; simp [ccT, cc]
  rw [h0, z, Matrix.J, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply,
    Matrix.fromBlocks_inj] at h
  obtain ⟨-, h2, h3, h4⟩ := h
  generalize γ.toBlocks₁₁ = A at *
  generalize γ.toBlocks₁₂ = B at *
  generalize γ.toBlocks₂₂ = D at *
  simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, Matrix.mul_one, Matrix.mul_neg,
    Matrix.neg_mul, neg_inj] at h2 h3 h4
  refine ⟨h2, ?_⟩
  have h5 : A * ccT D = 1 := mul_eq_one_comm.1 h3
  have h6 : D * ccT A = 1 := mul_eq_one_comm.1 h2
  have h7 : ccT D * B = ccT B * D := by rw [← sub_eq_zero, sub_eq_add_neg]; exact h4
  rw [Base.ccT_mul, Base.ccT_ccT]
  calc A * ccT B = A * (ccT B * D) * ccT A := by
        rw [Matrix.mul_assoc, Matrix.mul_assoc, h6, Matrix.mul_one]
    _ = B * ccT A := by rw [← h7, ← Matrix.mul_assoc, h5, Matrix.one_mul]
end GlobalTheory.SW.Parab
