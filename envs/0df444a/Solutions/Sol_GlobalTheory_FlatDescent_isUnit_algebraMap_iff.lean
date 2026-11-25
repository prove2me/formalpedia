-- Prove2me | solution 1 for GlobalTheory.FlatDescent.isUnit_algebraMap_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:43:38.716439+00:00
-- url     : https://prove2.me/submissions/44d50c35-28ab-4076-9573-cd56cf7561d6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_SpanSingletonEqTopIffIsUnitOfIsBaseChange
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_MemHomogIffIsHomogeneous
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsUniqueBaseChangeEqOfMem
import Theorems.Thm_GlobalTheory_Descent_algebraMap_dvd_iff


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
theorem _root_.solution [Module.FaithfullyFlat A B] (a : A) :
    IsUnit (algebraMap A B a) ↔ IsUnit a := by
  rw [isUnit_iff_dvd_one, isUnit_iff_dvd_one, ← Descent.algebraMap_dvd_iff B a 1, map_one]
end GlobalTheory.FlatDescent
