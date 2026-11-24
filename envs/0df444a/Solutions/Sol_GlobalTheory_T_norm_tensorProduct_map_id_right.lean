-- Prove2me | solution 1 for GlobalTheory.T.norm_tensorProduct_map_id_right
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:34:47.245824+00:00
-- url     : https://prove2.me/submissions/5164ce52-2da8-4cbe-bea4-18bd959f4b3b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_NormTensorProductMapLeft
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_NormTensorProductMapLeftStatement
import Theorems.Thm_GlobalTheory_norm_tensorProduct_map_left


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ {R B L : Type} [inst : Field R] [inst_1 : CommRing B] [inst_2 : Algebra R B] [inst_3 : Field L] [inst_4 : Algebra R L] [FiniteDimensional R L] (f : B →ₐ[R] B) (w : B ⊗[R] L), Algebra.norm B (Algebra.TensorProduct.map f (AlgHom.id R L) w) = f (Algebra.norm B w) := by
  first | exact @GlobalTheory.norm_tensorProduct_map_left | exact GlobalTheory.norm_tensorProduct_map_left | (intros; apply GlobalTheory.norm_tensorProduct_map_left <;> assumption)
end _root_.GlobalTheory.T
