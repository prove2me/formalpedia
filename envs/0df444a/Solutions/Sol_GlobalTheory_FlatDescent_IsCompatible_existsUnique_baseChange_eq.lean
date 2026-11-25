-- Prove2me | solution 1 for GlobalTheory.FlatDescent.IsCompatible.existsUnique_baseChange_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:42:50.302647+00:00
-- url     : https://prove2.me/submissions/00e9e4da-9800-485b-8c9b-fd5aa044d9ef

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_SpanSingletonEqTopIffIsUnitOfIsBaseChange
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_MemHomogIffIsHomogeneous
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsUniqueBaseChangeEqOfMem
import Theorems.Thm_GlobalTheory_FlatDescent_IsCompatible_map_mem
import Theorems.Thm_GlobalTheory_FlatDescent_existsUnique_baseChange_eq_of_mem
import Theorems.Thm_GlobalTheory_Descent_freeIso_hom
import Theorems.Thm_GlobalTheory_SymAlg_baseChangeEquiv_tmul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.Descent.freeIso_hom
attribute [local simp] GlobalTheory.SymAlg.baseChangeEquiv_tmul



set_option autoImplicit false
open TensorProduct
open GlobalTheory
open GlobalTheory.FlatDescent
variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
  {N : Type*} [AddCommGroup N] [Module A N] [Module B N] [IsScalarTower A B N]
  {N' : Type*} [AddCommGroup N'] [Module A N'] [Module B N'] [IsScalarTower A B N']
variable {M M' : Type*} [AddCommGroup M] [Module A M] [AddCommGroup M'] [Module A M']
namespace GlobalTheory.FlatDescent
namespace IsCompatible
theorem _root_.solution [Module.FaithfullyFlat A B]
    {f : B ⊗[A] M →ₗ[B] B ⊗[A] M'} (hf : IsCompatible (canonical B M) (canonical B M') f) :
    ∃! g : M →ₗ[A] M', g.baseChange B = f :=
  existsUnique_baseChange_eq_of_mem f fun m => hf.map_mem (by simp)
end IsCompatible
end GlobalTheory.FlatDescent
