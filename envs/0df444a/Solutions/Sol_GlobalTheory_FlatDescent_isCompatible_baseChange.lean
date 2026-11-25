-- Prove2me | solution 1 for GlobalTheory.FlatDescent.isCompatible_baseChange
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:45:05.390321+00:00
-- url     : https://prove2.me/submissions/8d794b5e-3d95-418c-8d6d-00da03b4c0db

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_SpanSingletonEqTopIffIsUnitOfIsBaseChange
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_MemHomogIffIsHomogeneous
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsUniqueBaseChangeEqOfMem
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
variable (B)
namespace GlobalTheory.FlatDescent
theorem _root_.solution (g : M →ₗ[A] M') :
    IsCompatible (canonical B M) (canonical B M') (g.baseChange B) := by
  intro x
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul b m => simp
end GlobalTheory.FlatDescent
