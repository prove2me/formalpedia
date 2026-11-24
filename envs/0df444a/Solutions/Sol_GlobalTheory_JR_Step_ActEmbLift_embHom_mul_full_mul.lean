-- Prove2me | solution 1 for GlobalTheory.JR.Step.ActEmbLift.embHom_mul_full_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T18:09:37.665809+00:00
-- url     : https://prove2.me/submissions/7cc9e8a9-0d9f-458e-8ea0-bdb60d5003b7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormMulApplyLeOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_BorderedConjugationDiagOneLiftBlockMatrix

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
noncomputable section
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.Step GlobalTheory.JR.Step.ActEmbLift
namespace GlobalTheory.JR.Step.ActEmbLift
theorem _root_.solution (k : Type) [CommRing k] (r : ℕ) (g h : Matrix (Fin r) (Fin r) k) (Z : Gl r k) :
    embHom r k g * full Z * embHom r k h = full (g * Z.1 * h, g *ᵥ Z.2.1, Z.2.2.1 ᵥ* h, Z.2.2.2) := by
  simp only [embHom, MonoidHom.coe_mk, OneHom.coe_mk, full, Matrix.reindex_apply]
  rw [Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
  congr 2
  · simp
  · ext i j; simp [Matrix.mul_apply, Matrix.mulVec, dotProduct]
  · ext i j; simp [Matrix.mul_apply, Matrix.vecMul, dotProduct]
  · ext i j; simp [Matrix.mul_apply]
end GlobalTheory.JR.Step.ActEmbLift
