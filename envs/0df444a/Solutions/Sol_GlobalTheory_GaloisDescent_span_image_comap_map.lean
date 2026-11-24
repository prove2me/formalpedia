-- Prove2me | solution 1 for GlobalTheory.GaloisDescent.span_image_comap_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T17:05:14.234841+00:00
-- url     : https://prove2.me/submissions/095df9e5-f5dd-417c-b4cf-2a17af8f6203

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsOneTmulOfForallFixed
import Theorems.Thm_GlobalTheory_GaloisDescent_contract_smul
import Theorems.Thm_GlobalTheory_GaloisDescent_mem_span_image_iff
import Theorems.Thm_GlobalTheory_GaloisDescent_contract_map
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
variable {V' M' : Type*} [AddCommGroup V'] [Module K V']
  [AddCommGroup M'] [Module K M'] [Module L M'] [IsScalarTower K L M'] {f' : V' →ₗ[K] M'}
namespace GlobalTheory.GaloisDescent
theorem _root_.solution (hf : IsBaseChange L f) (hf' : IsBaseChange L f') (p : V →ₗ[K] V')
    (F : M →ₗ[L] M') (hF : ∀ v, F (f v) = f' (p v)) (N : Submodule K V') :
    Submodule.span L (f '' N.comap p) = (Submodule.span L (f' '' N)).comap F := by
  ext x
  simp only [mem_span_image_iff hf, Submodule.mem_comap, mem_span_image_iff hf',
    contract_map hf hf' p F hF]
end GlobalTheory.GaloisDescent
