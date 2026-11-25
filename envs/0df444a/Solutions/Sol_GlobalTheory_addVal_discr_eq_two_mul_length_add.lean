-- Prove2me | solution 1 for GlobalTheory.addVal_discr_eq_two_mul_length_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:38:38.368209+00:00
-- url     : https://prove2.me/submissions/9a16a968-cfa4-4db3-b875-453e32c8a4d9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_LengthCommensurableSpanSpanOfDetNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_NatCardAlgHomEqFinrankOfIsReducedOfIsFractionRin
import Theorems.Thm_GlobalTheory_discr_eq_basis_det_sq_mul
import Theorems.Thm_GlobalTheory_length_quotient_span_eq_addVal_det


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
variable [IsDomain R] [IsDiscreteValuationRing R]
namespace GlobalTheory
theorem _root_.solution (e : Basis ι R S) (v : ι → S) :
    addVal R (Algebra.discr R v) =
      2 * Module.length R (S ⧸ Submodule.span R (Set.range v)) + addVal R (Algebra.discr R e) := by
  rw [discr_eq_basis_det_sq_mul e, addVal_mul, addVal_pow, length_quotient_span_eq_addVal_det e,
    nsmul_eq_mul, Nat.cast_ofNat]
end GlobalTheory
