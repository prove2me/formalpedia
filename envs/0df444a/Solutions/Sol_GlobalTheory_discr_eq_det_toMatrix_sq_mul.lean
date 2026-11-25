-- Prove2me | solution 1 for GlobalTheory.discr_eq_det_toMatrix_sq_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:24:45.86898+00:00
-- url     : https://prove2.me/submissions/69a53c46-70c8-41c8-a1a6-8db9013a7448

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_LengthCommensurableSpanSpanOfDetNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_NatCardAlgHomEqFinrankOfIsReducedOfIsFractionRin

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module IsDiscreteValuationRing Polynomial
open scoped TensorProduct
open GlobalTheory
variable {R S ι : Type*} [CommRing R] [CommRing S] [Algebra R S] [Fintype ι] [DecidableEq ι]
namespace GlobalTheory
theorem _root_.solution (e : Basis ι R S) (v : ι → S) :
    Algebra.discr R v = (e.toMatrix v).det ^ 2 * Algebra.discr R e := by
  rw [← Algebra.discr_of_matrix_vecMul, e.toMatrix_map_vecMul v]
end GlobalTheory
