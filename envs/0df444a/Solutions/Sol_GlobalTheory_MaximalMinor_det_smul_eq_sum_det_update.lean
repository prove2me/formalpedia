-- Prove2me | solution 1 for GlobalTheory.MaximalMinor.det_smul_eq_sum_det_update
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T18:54:33.372553+00:00
-- url     : https://prove2.me/submissions/0a567caf-0a3f-487d-bf1b-50090ac4c601

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_LinearIndependentOfDetMemNonZeroDivisors

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module Submodule Function
open GlobalTheory
open GlobalTheory.MaximalMinor
variable {A R F ι κ : Type*} [CommRing A] [CommRing R] [Algebra A R] [AddCommGroup F]
  [Module R F] [Module A F] [IsScalarTower A R F] [Fintype ι] [DecidableEq ι]
namespace GlobalTheory.MaximalMinor
theorem _root_.solution (b : Basis ι R F) (v : ι → F) (x : F) :
    b.det v • x = ∑ i, b.det (update v i x) • v i := by
  apply b.equivFun.injective
  have h := Matrix.mulVec_cramer (b.toMatrix v) (b.equivFun x)
  rw [map_smul, Basis.det_apply, ← h]
  ext j
  simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, Basis.equivFun_apply,
    smul_eq_mul, Matrix.mulVec, dotProduct, Matrix.cramer_apply, Basis.det_apply,
    Basis.toMatrix_update, Basis.toMatrix_apply, mul_comm]
end GlobalTheory.MaximalMinor
