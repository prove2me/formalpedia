-- Prove2me | solution 1 for GlobalTheory.algebraMap_discr_eq_det_sq_of_card
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T01:22:41.261112+00:00
-- url     : https://prove2.me/submissions/6fc2e587-6d0e-4df5-8952-6aa8c41fd8f2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_LengthCommensurableSpanSpanOfDetNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_NatCardAlgHomEqFinrankOfIsReducedOfIsFractionRin
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
variable [Module.Free R S] [Module.Finite R S]
namespace GlobalTheory
theorem _root_.solution (h : Fintype.card ι = finrank R S)
    {P : ι → (S →ₐ[R] L)} (hP : Function.Injective P) (v : ι → S) :
    algebraMap R L (Algebra.discr R v) = (Matrix.of fun i j => P j (v i)).det ^ 2 := by
  have := (algebraMap R L).domain_nontrivial
  exact algebraMap_discr_eq_det_sq_of_basis
    ((Module.finBasisOfFinrankEq R S h.symm).reindex (Fintype.equivFin ι).symm) hP v
end GlobalTheory
