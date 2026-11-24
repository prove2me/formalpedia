-- Prove2me | solution 1 for GlobalTheory.GaloisDescent.rationalPart_baseChange
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T16:49:32.200889+00:00
-- url     : https://prove2.me/submissions/5cf3f1aa-2c15-4a2d-8d1f-e9770169b501

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsOneTmulOfForallFixed
import Theorems.Thm_GlobalTheory_GaloisDescent_comap_span_image
import Theorems.Thm_GlobalTheory_GaloisDescent_baseChange_eq_span_image

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
variable {K L V G : Type*} [Field K] [Field L] [Algebra K L] [AddCommGroup V] [Module K V]
namespace GlobalTheory.GaloisDescent
theorem _root_.solution (N : Submodule K V) : rationalPart K (N.baseChange L) = N := by
  rw [baseChange_eq_span_image]
  exact comap_span_image (TensorProduct.isBaseChange K V L) N
end GlobalTheory.GaloisDescent
