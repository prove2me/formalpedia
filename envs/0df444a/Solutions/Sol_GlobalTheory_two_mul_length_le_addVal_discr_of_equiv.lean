-- Prove2me | solution 1 for GlobalTheory.two_mul_length_le_addVal_discr_of_equiv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:45:35.649925+00:00
-- url     : https://prove2.me/submissions/f78bb2ed-5e42-47bc-9873-032b85eef10a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_LengthCommensurableSpanSpanOfDetNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_NatCardAlgHomEqFinrankOfIsReducedOfIsFractionRin
import Theorems.Thm_GlobalTheory_addVal_discr_eq_two_mul_length_add_of_equiv

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
    2 * Module.length R (M ⧸ Submodule.span R (Set.range v)) ≤
      addVal R (Algebra.discr R fun i => φ (v i)) := by
  rw [addVal_discr_eq_two_mul_length_add_of_equiv φ e]
  exact le_self_add
end GlobalTheory
