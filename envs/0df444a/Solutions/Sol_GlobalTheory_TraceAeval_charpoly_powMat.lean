-- Prove2me | solution 1 for GlobalTheory.TraceAeval.charpoly_powMat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:37:23.943116+00:00
-- url     : https://prove2.me/submissions/80a50909-b5aa-432f-8134-5d02d8d7e40b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_TracePowerSumModEq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
open GlobalTheory GlobalTheory.TraceAeval
open Module
namespace GlobalTheory.TraceAeval
theorem _root_.solution {ψ : ℂ[X]} (h : ψ.Monic) : (powMat ψ.natDegree ψ).charpoly = ψ := by
  have h1 := charpoly_leftMulMatrix (AdjoinRoot.powerBasis' h)
  have h2 : minpoly ℂ (AdjoinRoot.powerBasis' h).gen = ψ := by
    rw [AdjoinRoot.powerBasis'_gen, AdjoinRoot.minpoly_root h.ne_zero, h.leadingCoeff]
    simp
  rw [h2] at h1
  refine Eq.trans ?_ h1
  congr 1
  ext i j
  refine Eq.trans ?_ (Algebra.leftMulMatrix_eq_repr_mul _ _ i j).symm
  have h3 := (AdjoinRoot.powerBasis' h).basis_eq_pow j
  refine Eq.trans ?_ (congrArg (fun t => (AdjoinRoot.powerBasis' h).basis.repr
    ((AdjoinRoot.powerBasis' h).gen * t) i) h3).symm
  simp only [← pow_succ']
  change _ = (AdjoinRoot.powerBasisAux' h).repr ((AdjoinRoot.root ψ) ^ ((j : ℕ) + 1)) i
  rw [AdjoinRoot.powerBasisAux'_repr_apply_to_fun, ← AdjoinRoot.mk_X, ← map_pow,
    AdjoinRoot.modByMonicHom_mk]
  rfl
end GlobalTheory.TraceAeval
