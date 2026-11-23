-- Prove2me | solution 1 for GlobalTheory.SW.HAct.blocks
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:45:49.903516+00:00
-- url     : https://prove2.me/submissions/c0718667-9fd6-490e-b284-adfccb9d6780

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_UnitaryActHalfSpace

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
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.HAct
variable {N : ℕ} {A B C D Z : Matrix (Fin N) (Fin N) ℂ}
namespace GlobalTheory.SW.HAct
theorem _root_.solution (h : (fromBlocks A B C D)ᴴ * Matrix.J (Fin N) ℂ * fromBlocks A B C D =
    Matrix.J (Fin N) ℂ) :
    Aᴴ * C = Cᴴ * A ∧ Aᴴ * D = Cᴴ * B + 1 ∧ Dᴴ * A = Bᴴ * C + 1 ∧ Bᴴ * D = Dᴴ * B := by
  rw [Matrix.J, fromBlocks_conjTranspose, fromBlocks_multiply, fromBlocks_multiply,
    fromBlocks_inj] at h
  simp only [Matrix.mul_zero, Matrix.mul_one, Matrix.mul_neg, zero_add, add_zero,
    Matrix.neg_mul] at h
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact (add_neg_eq_zero.1 h1).symm
  · rw [add_neg_eq_iff_eq_add.1 h2]; abel
  · rw [add_neg_eq_iff_eq_add.1 h3]; abel
  · exact (add_neg_eq_zero.1 h4).symm
end GlobalTheory.SW.HAct
