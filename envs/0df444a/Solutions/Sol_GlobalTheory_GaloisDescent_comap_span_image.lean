-- Prove2me | solution 1 for GlobalTheory.GaloisDescent.comap_span_image
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T16:30:35.42681+00:00
-- url     : https://prove2.me/submissions/425020c4-2d85-4f5a-b772-c3efa7c0bae7

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
theorem _root_.solution (hf : IsBaseChange L f) (N : Submodule K V) :
    ((Submodule.span L (f '' N)).restrictScalars K).comap f = N := by
  refine le_antisymm (fun v hv => ?_) fun v hv => Submodule.subset_span ⟨v, hv, rfl⟩
  obtain ⟨l, hl⟩ := Module.Projective.exists_dual_eq_one K (one_ne_zero (α := L))
  have := (mem_span_image_iff hf N _).1 hv l
  rwa [← one_smul L (f v), contract_smul, hl, one_smul] at this
end GlobalTheory.GaloisDescent
