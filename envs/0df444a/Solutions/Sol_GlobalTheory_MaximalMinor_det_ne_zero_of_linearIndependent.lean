-- Prove2me | solution 1 for GlobalTheory.MaximalMinor.det_ne_zero_of_linearIndependent
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T18:54:32.120844+00:00
-- url     : https://prove2.me/submissions/3f7e22a3-1db3-4211-9078-5b879d0d3b9d

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
theorem _root_.solution [IsDomain R] (b : Basis ι R F) {v : ι → F}
    (hv : LinearIndependent R v) : b.det v ≠ 0 := by
  intro h
  rw [Basis.det_apply] at h
  obtain ⟨c, hc, h0⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h
  refine hc (funext (Fintype.linearIndependent_iff.1 hv c ?_))
  apply b.equivFun.injective
  ext j
  simpa [Matrix.mulVec, dotProduct, Basis.toMatrix_apply, mul_comm] using congrFun h0 j
end GlobalTheory.MaximalMinor
