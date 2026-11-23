-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.QL.BlockMul.blocks_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:15:33.561538+00:00
-- url     : https://prove2.me/submissions/efd9313d-2232-4e23-bce2-82ca20314d08

import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_InstBorelGL
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_BlockMatrixMulBlocks

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix GlobalTheory.CompanionTheory.QL
open scoped ComplexConjugate ValuativeRel
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.QL GlobalTheory.CompanionTheory.QL.BlockMul
namespace GlobalTheory.CompanionTheory.QL.BlockMul
theorem _root_.solution : ∀ {F : Type} [Field F] (r d c e : ℕ) (x : Matrix (Fin (r + d)) (Fin (r + c)) F) (y : Matrix (Fin (r + c)) (Fin (r + e)) F), bAA (x * y) = bAA x * bAA y + bAD x * bDA y ∧ bAD (x * y) = bAA x * bAD y + bAD x * bDD y ∧ bDA (x * y) = bDA x * bAA y + bDD x * bDA y ∧ bDD (x * y) = bDA x * bAD y + bDD x * bDD y := by
  intro F _ r d c e x y
  refine ⟨?_, ?_, ?_, ?_⟩ <;> ext i j <;>
    simp only [bAA, bAD, bDA, bDD, Matrix.submatrix_apply, Matrix.add_apply, Matrix.mul_apply,
      Fin.sum_univ_add]
end GlobalTheory.CompanionTheory.QL.BlockMul
