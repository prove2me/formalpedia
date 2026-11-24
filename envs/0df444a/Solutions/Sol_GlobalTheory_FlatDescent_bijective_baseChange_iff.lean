-- Prove2me | solution 1 for GlobalTheory.FlatDescent.bijective_baseChange_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T15:09:47.945419+00:00
-- url     : https://prove2.me/submissions/4b2e2d4b-6f75-4b1d-a366-ad3816c56bf0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_SpanSingletonEqTopIffIsUnitOfIsBaseChange
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_MemHomogIffIsHomogeneous
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsUniqueBaseChangeEqOfMem

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
variable {M M' : Type*} [AddCommGroup M] [Module A M] [AddCommGroup M'] [Module A M']
variable (B)
namespace GlobalTheory.FlatDescent
theorem _root_.solution [Module.FaithfullyFlat A B] (g : M →ₗ[A] M') :
    Function.Bijective (g.baseChange B) ↔ Function.Bijective g :=
  Module.FaithfullyFlat.lTensor_bijective_iff_bijective A B g
end GlobalTheory.FlatDescent
