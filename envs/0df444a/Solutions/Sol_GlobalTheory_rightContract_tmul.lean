-- Prove2me | solution 1 for GlobalTheory.rightContract_tmul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:19:57.552458+00:00
-- url     : https://prove2.me/submissions/a1614bd3-57e9-48fa-8fea-6792e0877320

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_EigenTensorFullLeftSupport

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open TensorProduct
namespace GlobalTheory
theorem _root_.solution {F : Type} [Field F] {E E' : Type} [AddCommGroup E] [Module F E]
    [AddCommGroup E'] [Module F E'] (l : E' →ₗ[F] F) (x : E) (y : E') :
    rightContract l (x ⊗ₜ[F] y) = l y • x := by
  simp [rightContract]
end GlobalTheory
