-- Prove2me | solution 1 for GlobalTheory.SW.HermComp.row_rel
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:33:52.782463+00:00
-- url     : https://prove2.me/submissions/6915f4bb-da01-4c36-9a19-e2ce1f91d34b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_UnitaryActHalfSpaceStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_QuadCocycle

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
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.HermComp
variable {N : ℕ}
open Matrix Complex NumberField Filter Topology
open scoped ComplexConjugate ComplexOrder Real
variable {N : ℕ}
namespace GlobalTheory.SW.HermComp
namespace _root_.GlobalTheory.SW.HermComp
theorem _root_.solution (g : Matrix (Fin N ⊕ Fin N) (Fin N ⊕ Fin N) ℂ)
    (h : gᴴ * Matrix.J (Fin N) ℂ * g = Matrix.J (Fin N) ℂ) :
    g.toBlocks₁₁ * g.toBlocks₂₂ᴴ - g.toBlocks₁₂ * g.toBlocks₂₁ᴴ = 1 ∧
      g.toBlocks₂₂ * g.toBlocks₂₁ᴴ = g.toBlocks₂₁ * g.toBlocks₂₂ᴴ := by
  set J := Matrix.J (Fin N) ℂ
  have hJJ : J * J = -1 := Matrix.J_squared _ _
  have hleft : (-(J * gᴴ * J)) * g = 1 := by
    have : J * gᴴ * J * g = J * (gᴴ * J * g) := by simp only [Matrix.mul_assoc]
    rw [Matrix.neg_mul, this, h, hJJ, neg_neg]
  have hright : g * (-(J * gᴴ * J)) = 1 := mul_eq_one_comm.mp hleft
  have hgJ : g * J * gᴴ = J := by
    have h1 : g * J * gᴴ * J = -1 := by
      have := congrArg Neg.neg hright
      simpa [Matrix.mul_neg, Matrix.mul_assoc] using this
    calc g * J * gᴴ = g * J * gᴴ * J * (-J) := by
            rw [Matrix.mul_assoc (g * J * gᴴ), Matrix.mul_neg, hJJ, neg_neg, Matrix.mul_one]
      _ = J := by rw [h1, Matrix.neg_mul, Matrix.one_mul, neg_neg]
  rw [← Matrix.fromBlocks_toBlocks g] at hgJ
  simp only [J, Matrix.J, Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply,
    Matrix.fromBlocks_inj] at hgJ
  obtain ⟨-, h12, -, h22⟩ := hgJ
  simp only [Matrix.mul_zero, Matrix.mul_neg, Matrix.mul_one, zero_add, add_zero,
    Matrix.neg_mul] at h12 h22
  constructor
  · rw [← neg_inj, neg_sub, ← h12]; abel
  · rw [← sub_eq_zero, ← h22]; abel
end _root_.GlobalTheory.SW.HermComp
end GlobalTheory.SW.HermComp
