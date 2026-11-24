-- Prove2me | solution 1 for GlobalTheory.TopForm.IsFreeGen.repr_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T21:32:52.350334+00:00
-- url     : https://prove2.me/submissions/17dc0c39-7593-447f-abbc-5728d5be5dc2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_AlternatingMapSumSmulEqDetSmul
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ExistsAlgHomOfIsBaseChange

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open scoped TensorProduct
open GlobalTheory
open GlobalTheory.TopForm
variable {A M : Type*} [CommRing A] [AddCommGroup M] [Module A M] {ω : M}
namespace GlobalTheory.TopForm
namespace IsFreeGen
theorem _root_.solution (h : IsFreeGen A ω) (x : M) : h.repr x • ω = x :=
  h.repr.symm_apply_apply x
end IsFreeGen
end GlobalTheory.TopForm
