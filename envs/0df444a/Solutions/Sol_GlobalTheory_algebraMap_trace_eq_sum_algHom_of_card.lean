-- Prove2me | solution 1 for GlobalTheory.algebraMap_trace_eq_sum_algHom_of_card
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:55:21.072901+00:00
-- url     : https://prove2.me/submissions/dfbdd3fe-c138-4c4a-af34-d4d21ce8f2d3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_LengthCommensurableSpanSpanOfDetNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_NatCardAlgHomEqFinrankOfIsReducedOfIsFractionRin
import Theorems.Thm_GlobalTheory_algebraMap_trace_eq_sum_algHom_of_basis

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
variable [Module.Free R S] [Module.Finite R S]
omit [DecidableEq ι]
namespace GlobalTheory
theorem _root_.solution (h : Fintype.card ι = finrank R S)
    {P : ι → (S →ₐ[R] L)} (hP : Function.Injective P) (x : S) :
    algebraMap R L (Algebra.trace R S x) = ∑ j, P j x := by
  classical
  have := (algebraMap R L).domain_nontrivial
  exact algebraMap_trace_eq_sum_algHom_of_basis
    ((Module.finBasisOfFinrankEq R S h.symm).reindex (Fintype.equivFin ι).symm) hP x
end GlobalTheory
