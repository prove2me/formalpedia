-- Prove2me | solution 1 for GlobalTheory.GenEigen.exists_ge
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:27:23.360643+00:00
-- url     : https://prove2.me/submissions/400d7faa-faae-4f13-9cb4-cdbb877f5d6e

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_GeNatCast
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_EigenvectorOfGeneralizedEigenUnramified

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped BigOperators TensorProduct
open Formalism.L2.FormalSeriesBounds
open GlobalTheory GlobalTheory.GenEigen
variable {C : Type} [Field C] {V : VF C}
namespace GlobalTheory.GenEigen
theorem _root_.solution (z : C) : ∃ m : ℝ, V.Ge m z := by
  unfold VF.Ge
  induction V.v z using WithTop.recTopCoe with
  | top => exact ⟨0, le_top⟩
  | coe t => exact ⟨t, le_rfl⟩
end GlobalTheory.GenEigen
