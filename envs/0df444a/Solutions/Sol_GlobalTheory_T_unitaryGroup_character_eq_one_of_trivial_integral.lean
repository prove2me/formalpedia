-- Prove2me | solution 1 for GlobalTheory.T.unitaryGroup_character_eq_one_of_trivial_integral
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T18:26:07.507127+00:00
-- url     : https://prove2.me/submissions/f5aee2e0-54d0-4e9a-8173-416bea46331c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnitaryGroupCharacterEqOneOfTrivialIntegral
import Definitions.Def_Formalism_SatakeDualWeyl_StatementF
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnitaryGroupCharacterEqOneOfTrivialIntegralStatement
import Theorems.Thm_GlobalTheory_UnitaryCharacter_char_eq_one


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.UG
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (L : Type) [Field L] [CharZero L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L) (σ : L →+* L) (q n : ℕ) (J : GL (Fin n) L), IsUnramInv ϖ σ q → Valued.v (2 : L) = 1 → J ∈ GLint (Fin n) (intL L) → (∀ i j, σ ((J : Matrix (Fin n) (Fin n) L) i j) = (J : Matrix (Fin n) (Fin n) L) j i) → ∀ ν : UJ σ (J : Matrix (Fin n) (Fin n) L) →* Circle, (∀ k : UJ σ (J : Matrix (Fin n) (Fin n) L), (k : GL (Fin n) L) ∈ GLint (Fin n) (intL L) → ν k = 1) → ∀ g, ν g = 1 := by
  first | exact @GlobalTheory.UnitaryCharacter.char_eq_one | exact GlobalTheory.UnitaryCharacter.char_eq_one | (intros; apply GlobalTheory.UnitaryCharacter.char_eq_one <;> assumption)
end _root_.GlobalTheory.T
