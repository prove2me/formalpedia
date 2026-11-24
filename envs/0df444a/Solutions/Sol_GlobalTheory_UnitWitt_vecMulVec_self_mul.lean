-- Prove2me | solution 1 for GlobalTheory.UnitWitt.vecMulVec_self_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:05:09.865214+00:00
-- url     : https://prove2.me/submissions/778ab65d-d582-4bdb-8e91-a991e01a1aec

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ConjTransposeVecMulVecSelf

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
open GlobalTheory GlobalTheory.UnitWitt
variable {E : Type} [Field E] [StarRing E] {r : ℕ}
namespace GlobalTheory.UnitWitt
theorem _root_.solution (w : Fin r → E) :
    vecMulVec w (star w) * vecMulVec w (star w) = (star w ⬝ᵥ w) • vecMulVec w (star w) := by
  ext i j
  simp only [mul_apply, vecMulVec_apply, Matrix.smul_apply, smul_eq_mul, dotProduct, Pi.star_apply, Finset.sum_mul,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  ring
end GlobalTheory.UnitWitt
