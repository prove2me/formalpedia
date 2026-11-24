-- Prove2me | solution 1 for GlobalTheory.det_points_sq_eq_discr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:34:47.64017+00:00
-- url     : https://prove2.me/submissions/5bb2d982-af77-4728-ab69-52c070c94242

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_LinearIndependentRealOfIntOfDiscrete
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_NormDetMulProdSqLeOfEntryLe
import Theorems.Thm_GlobalTheory_algebraMap_trace_eq_sum_points

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct Matrix
open Module Algebra
open GlobalTheory
variable {R S : Type*} (E : Type*) [CommRing R] [CommRing S] [Algebra R S] [Field E]
  [Algebra R E] [IsFiniteSplit E (E ⊗[R] S)]
variable [Module.Free R S]
variable {E} {ι : Type*} [Fintype ι]
variable [Module.Finite R S]
variable [DecidableEq ι]
namespace GlobalTheory
theorem _root_.solution (P : ι ≃ (S →ₐ[R] E)) (v : ι → S) :
    (Matrix.of fun i j ↦ P j (v i)).det ^ 2 = algebraMap R E (discr R v) := by
  have : (algebraMap R E).mapMatrix (traceMatrix R v) =
      (Matrix.of fun i j ↦ P j (v i)) * (Matrix.of fun i j ↦ P j (v i))ᵀ := by
    ext i j
    simp [Matrix.mul_apply, algebraMap_trace_eq_sum_points P]
  rw [discr_def, RingHom.map_det, this, Matrix.det_mul, Matrix.det_transpose, pow_two]
end GlobalTheory
