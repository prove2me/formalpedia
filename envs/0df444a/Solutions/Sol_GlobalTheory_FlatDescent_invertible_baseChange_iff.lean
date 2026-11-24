-- Prove2me | solution 1 for GlobalTheory.FlatDescent.invertible_baseChange_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T16:08:50.663801+00:00
-- url     : https://prove2.me/submissions/826f29c8-fee6-4082-adc9-60e57f0dc03c

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
variable (B)
namespace GlobalTheory.FlatDescent
theorem _root_.solution [Module.FaithfullyFlat A B] (M : Type*) [AddCommGroup M]
    [Module A M] : Module.Invertible B (B ⊗[A] M) ↔ Module.Invertible A M :=
  ⟨fun _ => invertible_of_isBaseChange (TensorProduct.isBaseChange A M B), fun _ => inferInstance⟩
end GlobalTheory.FlatDescent
