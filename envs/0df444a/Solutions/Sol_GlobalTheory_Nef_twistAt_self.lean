-- Prove2me | solution 1 for GlobalTheory.Nef.twistAt_self
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T01:00:49.280721+00:00
-- url     : https://prove2.me/submissions/f2906949-e37d-4027-b746-56183ebcc55d

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
    (h : Place k F → Matrix (Fin n) (Fin n) F) : twistAt v₀ c h v₀ = c • h v₀ := by
  simp [twistAt]
end GlobalTheory.Nef
