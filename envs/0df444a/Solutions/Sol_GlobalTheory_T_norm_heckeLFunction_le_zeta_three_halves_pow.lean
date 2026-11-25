-- Prove2me | solution 1 for GlobalTheory.T.norm_heckeLFunction_le_zeta_three_halves_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T18:26:44.474021+00:00
-- url     : https://prove2.me/submissions/787df241-aa2c-4475-b40e-f8b02fb89db8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormHeckeLFunctionLeZetaThreeHalvesPow
import Definitions.Def_Formalism_PairingDivisors_StatementA
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsFinSetSplitPlacesCoprimeConductor
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormHeckeLFunctionLeZetaThreeHalvesPowStatement

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.CMVal
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (E : Type) [Field E] [NumberField E] (χ : HChar E) (Λ : ℂ → ℂ) (S : ℂ), IsUnitary χ → IsHeckeL χ Λ → 3 / 2 ≤ S.re → ‖Λ S‖ ≤ ‖riemannZeta (3 / 2)‖ ^ Module.finrank ℚ E := by
  first | exact @GlobalTheory.HeckeLBound.norm_heckeL_le | exact GlobalTheory.HeckeLBound.norm_heckeL_le | (intros; apply GlobalTheory.HeckeLBound.norm_heckeL_le <;> assumption)
end _root_.GlobalTheory.T
