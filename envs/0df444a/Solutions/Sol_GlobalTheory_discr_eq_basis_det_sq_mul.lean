-- Prove2me | solution 1 for GlobalTheory.discr_eq_basis_det_sq_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:32:37.805898+00:00
-- url     : https://prove2.me/submissions/f0b7792b-17a9-497d-a20e-059ab25de1d5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_LengthCommensurableSpanSpanOfDetNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_NatCardAlgHomEqFinrankOfIsReducedOfIsFractionRin
import Theorems.Thm_GlobalTheory_discr_eq_det_toMatrix_sq_mul

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
    Algebra.discr R v = e.det v ^ 2 * Algebra.discr R e := by
  rw [discr_eq_det_toMatrix_sq_mul e, Basis.det_apply]
end GlobalTheory
