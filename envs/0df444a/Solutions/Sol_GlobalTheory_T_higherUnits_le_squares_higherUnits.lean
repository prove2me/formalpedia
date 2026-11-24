-- Prove2me | solution 1 for GlobalTheory.T.higherUnits_le_squares_higherUnits
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T21:13:38.504948+00:00
-- url     : https://prove2.me/submissions/b37f38ae-ffc6-4788-8d6c-dd346e47063c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_HigherUnitsLeSquaresHigherUnits
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_SqSubLeNormSub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_HigherUnitsLeSquaresHigherUnitsStatement
import Theorems.Thm_GlobalTheory_QNorm_hiUnits_le_sqs_hiUnits


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (e : ℕ), Valued.v (2 : v.adicCompletion F) = WithZero.exp (-(e : ℤ)) → hiUnits (Valued.v : Valuation (v.adicCompletion F) ℤᵐ⁰) (2 * e + 1) ≤ sqs (hiUnits (Valued.v : Valuation (v.adicCompletion F) ℤᵐ⁰) (e + 1)) := by
  first | exact @GlobalTheory.QNorm.hiUnits_le_sqs_hiUnits | exact GlobalTheory.QNorm.hiUnits_le_sqs_hiUnits | (intros; apply GlobalTheory.QNorm.hiUnits_le_sqs_hiUnits <;> assumption)
end _root_.GlobalTheory.T
