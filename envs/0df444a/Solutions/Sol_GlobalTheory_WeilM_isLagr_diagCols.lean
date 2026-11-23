-- Prove2me | solution 1 for GlobalTheory.WeilM.isLagr_diagCols
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:12:08.5878+00:00
-- url     : https://prove2.me/submissions/d426f3f9-f3e4-45f8-97d4-ed190051c989

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MatrixMeasurableSpace
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain MeasureTheory Matrix
open scoped NNReal Classical
open GlobalTheory GlobalTheory.WeilM
variable {R : Type} [CommRing R] {E : Type} [CommRing E] [Algebra R E] (c : E →ₐ[R] E)
variable {c}
variable (c)
variable {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
variable [Invertible (2 : R)]
namespace GlobalTheory.WeilM
theorem _root_.solution (JB : Matrix β β E) : IsLagr c (dbl JB) (diagCols β : Matrix (β ⊕ β) β E) := by
  have h2 : algebraMap R E (⅟(2 : R)) + algebraMap R E (⅟(2 : R)) = 1 := by
    rw [← map_add, invOf_two_add_invOf_two, map_one]
  have h1 : (1 : Matrix β β E).map c = 1 := Matrix.map_one _ (map_zero c) (map_one c)
  have h1' : (-1 : Matrix β β E).map c = -1 := by rw [Matrix.map_neg _ (map_neg c), h1]
  have h3 : ∀ s : Matrix β β E, (fromRows 1 s : Matrix (β ⊕ β) β E).map c = fromRows 1 (s.map c) := fun s => by
    rw [fromRows_map, h1]
  refine ⟨?_, fromRows 1 (-1), algebraMap R E (⅟(2 : R)) • fromBlocks 1 1 1 (-1), ?_, ?_, ?_⟩
  · simp [diagCols, dbl, h3, h1, transpose_fromRows, fromCols_mul_fromBlocks, fromCols_mul_fromRows]
  · simp [dbl, h3, h1', transpose_fromRows, fromCols_mul_fromBlocks, fromCols_mul_fromRows]
  · rw [diagCols, fromCols_fromRows_eq_fromBlocks, Matrix.mul_smul, fromBlocks_multiply, fromBlocks_smul, ← fromBlocks_one]
    simp [← add_smul, h2]
  · rw [diagCols, fromCols_fromRows_eq_fromBlocks, Matrix.smul_mul, fromBlocks_multiply, fromBlocks_smul, ← fromBlocks_one]
    simp [← add_smul, h2]
end GlobalTheory.WeilM
