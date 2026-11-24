-- Prove2me | solution 1 for GlobalTheory.FlatDescent.IsCompatible.map_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T15:09:43.682882+00:00
-- url     : https://prove2.me/submissions/cfd07dbc-2c7a-4abd-a0a4-7413c6e0e541

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
namespace GlobalTheory.FlatDescent
namespace IsCompatible
theorem _root_.solution {θ : N →ₗ[B] B ⊗[A] N} {θ' : N' →ₗ[B] B ⊗[A] N'} {f : N →ₗ[B] N'}
    (hf : IsCompatible θ θ' f) {n : N} (hn : n ∈ invariants θ) : f n ∈ invariants θ' := by
  rw [mem_invariants] at hn ⊢
  rw [hf n, hn]
  simp
end IsCompatible
end GlobalTheory.FlatDescent
