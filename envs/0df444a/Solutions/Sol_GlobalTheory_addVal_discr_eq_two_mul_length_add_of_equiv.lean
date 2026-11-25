-- Prove2me | solution 1 for GlobalTheory.addVal_discr_eq_two_mul_length_add_of_equiv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:49:13.619199+00:00
-- url     : https://prove2.me/submissions/7654c8ff-d93e-4175-9212-10f207d2a885

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_LengthCommensurableSpanSpanOfDetNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_NatCardAlgHomEqFinrankOfIsReducedOfIsFractionRin
import Theorems.Thm_GlobalTheory_addVal_discr_eq_two_mul_length_add

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
theorem _root_.solution {M : Type*} [AddCommGroup M] [Module R M]
    (φ : M ≃ₗ[R] S) (e : Basis ι R S) (v : ι → M) :
    addVal R (Algebra.discr R fun i => φ (v i)) =
      2 * Module.length R (M ⧸ Submodule.span R (Set.range v)) + addVal R (Algebra.discr R e) := by
  rw [addVal_discr_eq_two_mul_length_add e,
    (Submodule.Quotient.equiv (Submodule.span R (Set.range v))
      (Submodule.span R (Set.range fun i => φ (v i))) φ ?_).length_eq]
  rw [Submodule.map_span, ← Set.range_comp]
  rfl
end GlobalTheory
