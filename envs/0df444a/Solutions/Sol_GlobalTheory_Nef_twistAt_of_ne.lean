-- Prove2me | solution 1 for GlobalTheory.Nef.twistAt_of_ne
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T01:01:45.827077+00:00
-- url     : https://prove2.me/submissions/c6ebf96a-6fc5-4b82-b065-97a498e3dec4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsAdmissibleIntegralBasisChangeOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_TwistAtOfNe
import Theorems.Thm_GroundTheory_FunctionField_Place_ordHom_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.FunctionField.Place.ordHom_apply



set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open Polynomial
open GlobalTheory GlobalTheory.Nef
namespace GlobalTheory.Nef
theorem _root_.solution {k F : Type} [Field k] [Field F] [Algebra k F] {n : ℕ} (v₀ : Place k F) (c : F)
    (h : Place k F → Matrix (Fin n) (Fin n) F) (v : Place k F) (hv : v ≠ v₀) :
    twistAt v₀ c h v = h v := by
  simp [twistAt, hv]
end GlobalTheory.Nef
