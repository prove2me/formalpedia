-- Prove2me | solution 1 for GlobalTheory.GaloisDescent.span_image_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:44:23.093858+00:00
-- url     : https://prove2.me/submissions/c88cb602-7539-4026-9d66-a2f142bf5458

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsOneTmulOfForallFixed
import Theorems.Thm_GlobalTheory_GaloisDescent_comap_span_image

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct Module
open GlobalTheory GlobalTheory.GaloisDescent
variable {K L V M G : Type*} [Field K] [Field L] [Algebra K L] [AddCommGroup V] [Module K V]
  [AddCommGroup M] [Module K M] [Module L M] [IsScalarTower K L M] {f : V →ₗ[K] M}
namespace GlobalTheory.GaloisDescent
theorem _root_.solution (hf : IsBaseChange L f) :
    Function.Injective fun N : Submodule K V => Submodule.span L (f '' N) := fun N N' h => by
  rw [← comap_span_image hf N, ← comap_span_image hf N']
  exact congrArg (fun W : Submodule L M => (W.restrictScalars K).comap f) h
end GlobalTheory.GaloisDescent
