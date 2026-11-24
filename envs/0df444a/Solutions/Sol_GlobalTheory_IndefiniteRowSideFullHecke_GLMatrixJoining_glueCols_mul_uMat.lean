-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.GLMatrixJoining.glueCols_mul_uMat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T17:38:41.36029+00:00
-- url     : https://prove2.me/submissions/4f702d86-e7d5-4266-ac8d-57dc9d7c16f4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MatrixMeasurableSpace
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TorsionBlocks_GL2CharacterZeros

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix GlobalTheory.SplitWeil
noncomputable section
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.GLMatrixJoining
variable {k : Type} [Field k]
variable {ρ v W : Type} [Fintype ρ] [DecidableEq ρ] [Fintype v] [DecidableEq v]
namespace GlobalTheory.IndefiniteRowSideFullHecke.GLMatrixJoining
theorem _root_.solution (ξ : Matrix W ρ k) (x₀ : Matrix W v k) (c : Matrix W ρ k)
    (ν : Matrix v ρ k) (ν' : Matrix ρ v k) (b : Matrix ρ ρ k) :
    glueCols ξ x₀ c * uMat ν ν' b = glueCols ξ (x₀ + ξ * ν') (c + ξ * b + x₀ * ν) := by
  simp only [glueCols, uMat, fromCols_mul_fromBlocks, mul_fromCols, Matrix.mul_one, Matrix.mul_zero,
    add_zero]
  ext i (j | j | j) <;> simp [add_comm, add_left_comm, add_assoc]
end GlobalTheory.IndefiniteRowSideFullHecke.GLMatrixJoining
