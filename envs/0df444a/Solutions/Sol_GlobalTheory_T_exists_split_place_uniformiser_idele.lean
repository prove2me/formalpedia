-- Prove2me | solution 1 for GlobalTheory.T.exists_split_place_uniformiser_idele
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T21:07:50.420818+00:00
-- url     : https://prove2.me/submissions/6e4dc34a-7e7e-4956-ac0f-f142c962ecf8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsSplitPlaceUniformiserIdele
import Definitions.Def_Formalism_PairingDivisors_StatementA
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsFinSetSplitPlacesCoprimeConductor
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ValIotaLeOfMem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsSplitPlaceUniformiserIdeleStatement
import Theorems.Thm_GlobalTheory_CMVal_Euler_exists_split_unif_idele


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.CMVal.Euler
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (v : HeightOneSpectrum (OF E)) (x : OF E), Splits v → (∀ P, Over P v → Valued.v (iota x P) = WithZero.exp (-1 : ℤ)) → ∃ π : (Af E)ˣ, (∀ P, Over P v → (π : Af E) P = iota x P) ∧ (∀ P, ¬ Over P v → (π : Af E) P = 1) ∧ modF π = ((Ideal.absNorm v.asIdeal : ℕ) : ℝ)⁻¹ ^ 2 ∧ ∀ χ : HChar E, TrivOnF χ → finPart χ π = 1 := by
  first | exact @GlobalTheory.CMVal.Euler.exists_split_unif_idele | exact GlobalTheory.CMVal.Euler.exists_split_unif_idele | (intros; apply GlobalTheory.CMVal.Euler.exists_split_unif_idele <;> assumption)
end _root_.GlobalTheory.T
