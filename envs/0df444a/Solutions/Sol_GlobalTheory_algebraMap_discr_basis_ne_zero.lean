-- Prove2me | solution 1 for GlobalTheory.algebraMap_discr_basis_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T01:20:52.546055+00:00
-- url     : https://prove2.me/submissions/2d000dcb-0e85-4538-bf63-53d6b33a9988

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_LengthCommensurableSpanSpanOfDetNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_NatCardAlgHomEqFinrankOfIsReducedOfIsFractionRin
import Theorems.Thm_GlobalTheory_det_algHom_basis_ne_zero
import Theorems.Thm_GlobalTheory_algebraMap_discr_eq_det_sq_of_basis

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
variable {R S L ι : Type*} [CommRing R] [CommRing S] [Algebra R S] [CommRing L] [IsDomain L]
  [Algebra R L] [Fintype ι] [DecidableEq ι]
namespace GlobalTheory
theorem _root_.solution (e : Basis ι R S) {P : ι → (S →ₐ[R] L)}
    (hP : Function.Injective P) : algebraMap R L (Algebra.discr R e) ≠ 0 := by
  rw [algebraMap_discr_eq_det_sq_of_basis e hP]
  exact pow_ne_zero _ (det_algHom_basis_ne_zero e hP)
end GlobalTheory
