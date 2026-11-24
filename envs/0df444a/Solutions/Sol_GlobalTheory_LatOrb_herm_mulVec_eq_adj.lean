-- Prove2me | solution 1 for GlobalTheory.LatOrb.herm_mulVec_eq_adj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T18:37:32.957583+00:00
-- url     : https://prove2.me/submissions/b0024396-657e-4d96-a968-4da5179b0c43

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MemMatLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MatrixImageAdjointMulEqOfSelfDualLattices

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial Matrix GlobalTheory.LatOrb
open GlobalTheory GlobalTheory.LatOrb
namespace GlobalTheory.LatOrb
theorem _root_.solution {K : Type} [Field K] (σ : K →+* K)
    {n : ℕ} (x : Matrix (Fin n) (Fin n) K) (y m : Fin n → K) :
    herm σ y (x *ᵥ m) = herm σ ((x.map σ)ᵀ *ᵥ y) m := by
  simp only [herm, Matrix.mulVec, dotProduct, map_sum, map_mul, Matrix.transpose_apply,
    Matrix.map_apply, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
  ring
end GlobalTheory.LatOrb
