-- Prove2me | solution 1 for GlobalTheory.two_mul_length_le_addVal_discr_of_card
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:44:14.641404+00:00
-- url     : https://prove2.me/submissions/5841a076-4e73-48a7-bd73-2f93ceaffbbd

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_LengthCommensurableSpanSpanOfDetNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_NatCardAlgHomEqFinrankOfIsReducedOfIsFractionRin
import Theorems.Thm_GlobalTheory_two_mul_length_le_addVal_discr

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
theorem _root_.solution [Module.Free R S] [Module.Finite R S]
    (h : Fintype.card ι = finrank R S) (v : ι → S) :
    2 * Module.length R (S ⧸ Submodule.span R (Set.range v)) ≤ addVal R (Algebra.discr R v) :=
  two_mul_length_le_addVal_discr (Module.finBasisOfFinrankEq R S h.symm |>.reindex
    (Fintype.equivFin ι).symm) v
end GlobalTheory
