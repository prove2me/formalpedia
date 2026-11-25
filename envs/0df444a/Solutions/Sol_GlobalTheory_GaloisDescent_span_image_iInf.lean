-- Prove2me | solution 1 for GlobalTheory.GaloisDescent.span_image_iInf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:44:19.456365+00:00
-- url     : https://prove2.me/submissions/12154f13-651c-4521-9924-6528f3d0b7da

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsOneTmulOfForallFixed
import Theorems.Thm_GlobalTheory_GaloisDescent_contract_smul
import Theorems.Thm_GlobalTheory_GaloisDescent_mem_span_image_iff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.GaloisDescent.contract_smul

set_option autoImplicit false
open TensorProduct Module
open GlobalTheory GlobalTheory.GaloisDescent
variable {K L V M G : Type*} [Field K] [Field L] [Algebra K L] [AddCommGroup V] [Module K V]
  [AddCommGroup M] [Module K M] [Module L M] [IsScalarTower K L M] {f : V →ₗ[K] M}
namespace GlobalTheory.GaloisDescent
theorem _root_.solution (hf : IsBaseChange L f) {J : Sort*} (N : J → Submodule K V) :
    Submodule.span L (f '' (⨅ j, N j : Submodule K V)) = ⨅ j, Submodule.span L (f '' N j) := by
  ext x
  simp only [mem_span_image_iff hf, Submodule.mem_iInf]
  exact forall_comm
end GlobalTheory.GaloisDescent
