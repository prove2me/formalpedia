-- Prove2me | solution 1 for GlobalTheory.two_mul_length_le_addVal_discr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:55:31.031031+00:00
-- url     : https://prove2.me/submissions/72811c02-5a39-4050-8f55-4a76a025f6b9

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
theorem _root_.solution (e : Basis ι R S) (v : ι → S) :
    2 * Module.length R (S ⧸ Submodule.span R (Set.range v)) ≤ addVal R (Algebra.discr R v) := by
  rw [addVal_discr_eq_two_mul_length_add e]
  exact le_self_add
end GlobalTheory
