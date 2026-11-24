-- Prove2me | solution 1 for GlobalTheory.FlatDescent.IsDescentDatum.invertible_invariants
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T16:04:50.17208+00:00
-- url     : https://prove2.me/submissions/31493db8-8d1b-4472-ac5d-581e8d844231

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_SpanSingletonEqTopIffIsUnitOfIsBaseChange
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_MemHomogIffIsHomogeneous
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsUniqueBaseChangeEqOfMem
import Theorems.Thm_GlobalTheory_FlatDescent_IsDescentDatum_isBaseChange
import Theorems.Thm_GlobalTheory_FlatDescent_invertible_of_isBaseChange

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct
open GlobalTheory
open GlobalTheory.FlatDescent
variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
  {N : Type*} [AddCommGroup N] [Module A N] [Module B N] [IsScalarTower A B N]
  {N' : Type*} [AddCommGroup N'] [Module A N'] [Module B N'] [IsScalarTower A B N']
namespace GlobalTheory.FlatDescent
namespace IsDescentDatum
theorem _root_.solution [Module.FaithfullyFlat A B]
    {θ : N →ₗ[B] B ⊗[A] N} (h : IsDescentDatum θ) [Module.Invertible B N] :
    Module.Invertible A (invariants θ) :=
  invertible_of_isBaseChange h.isBaseChange
end IsDescentDatum
end GlobalTheory.FlatDescent
