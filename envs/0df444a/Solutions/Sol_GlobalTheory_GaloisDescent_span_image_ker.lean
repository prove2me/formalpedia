-- Prove2me | solution 1 for GlobalTheory.GaloisDescent.span_image_ker
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:44:27.240678+00:00
-- url     : https://prove2.me/submissions/4764f835-69a7-480f-9428-7acbfc52d2a3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsOneTmulOfForallFixed
import Theorems.Thm_GlobalTheory_GaloisDescent_contract_smul
import Theorems.Thm_GlobalTheory_GaloisDescent_span_image_comap_map
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
    (F : M →ₗ[L] M') (hF : ∀ v, F (f v) = f' (p v)) :
    Submodule.span L (f '' LinearMap.ker p) = LinearMap.ker F := by
  rw [← Submodule.comap_bot, span_image_comap_map hf hf' p F hF]
  simp
end GlobalTheory.GaloisDescent
