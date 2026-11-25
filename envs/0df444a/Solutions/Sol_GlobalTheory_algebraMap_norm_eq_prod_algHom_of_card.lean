-- Prove2me | solution 1 for GlobalTheory.algebraMap_norm_eq_prod_algHom_of_card
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:45:36.97558+00:00
-- url     : https://prove2.me/submissions/d779b448-f2a8-4b05-917d-3a1f05b61619

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_LengthCommensurableSpanSpanOfDetNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_NatCardAlgHomEqFinrankOfIsReducedOfIsFractionRin
import Theorems.Thm_GlobalTheory_algebraMap_norm_eq_prod_algHom_of_basis

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
    algebraMap R L (Algebra.norm R x) = ∏ j, P j x := by
  classical
  have := (algebraMap R L).domain_nontrivial
  exact algebraMap_norm_eq_prod_algHom_of_basis
    ((Module.finBasisOfFinrankEq R S h.symm).reindex (Fintype.equivFin ι).symm) hP x
end GlobalTheory
