-- Prove2me | solution 1 for GlobalTheory.discr_norm_trace_of_isReduced
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T04:37:03.7281+00:00
-- url     : https://prove2.me/submissions/2344ec3b-b7e1-45e7-b780-928092dafe8c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_LengthCommensurableSpanSpanOfDetNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_NatCardAlgHomEqFinrankOfIsReducedOfIsFractionRin
import Theorems.Thm_GlobalTheory_card_eq_finrank_of_equiv_algHom
import Theorems.Thm_GlobalTheory_algebraMap_norm_eq_prod_of_equiv_algHom
import Theorems.Thm_GlobalTheory_algebraMap_trace_eq_sum_of_equiv_algHom
import Theorems.Thm_GlobalTheory_algebraMap_discr_eq_det_sq_of_equiv_algHom

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
variable {K S L ι : Type*} [Field K] [PerfectField K] [CommRing S] [Algebra K S]
  [Module.Finite K S] [IsReduced S] [Field L] [Algebra K L] [IsSepClosed L] [Fintype ι]
  [DecidableEq ι]
namespace GlobalTheory
theorem _root_.solution (P : ι ≃ (S →ₐ[K] L)) :
    Fintype.card ι = finrank K S ∧
    (∀ v : ι → S, algebraMap K L (Algebra.discr K v) = (Matrix.of fun i j => P j (v i)).det ^ 2) ∧
    (∀ x : S, algebraMap K L (Algebra.norm K x) = ∏ j, P j x) ∧
    (∀ x : S, algebraMap K L (Algebra.trace K S x) = ∑ j, P j x) :=
  have := etale_of_isReduced_of_perfectField K S
  ⟨card_eq_finrank_of_equiv_algHom P, algebraMap_discr_eq_det_sq_of_equiv_algHom P,
    algebraMap_norm_eq_prod_of_equiv_algHom P, algebraMap_trace_eq_sum_of_equiv_algHom P⟩
end GlobalTheory
