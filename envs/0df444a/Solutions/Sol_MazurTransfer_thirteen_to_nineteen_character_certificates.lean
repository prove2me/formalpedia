-- Prove2me | solution 1 for MazurTransfer.thirteen_to_nineteen_character_certificates
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-18T23:30:37.287335+00:00
-- url     : https://prove2.me/submissions/8d1cf67d-bf7e-4e9f-953d-6b5ab0abc66b

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: explicit inverse order-six characters from the thirteenth
cyclotomic Galois group (ZMod 13)^* to F19^*, normalized at two.
Named downstream consumer: the two actual norm-factor arithmetic13 lines.
-/
import Mathlib
import Definitions.Def_MazurTransfer_ThirteenToNineteenOriginalCharacterDataAndConstructorCertificates20261018
open MazurTransfer.ThirteenToNineteenCharacters
attribute [local instance] characterOriginalPrime13Provider20261018 characterOriginalPrime19Provider20261018
namespace MazurTransfer.ThirteenToNineteenCharacterProofHelpers20261018
theorem character_generator : (character generator : ZMod 19) = 12 := by decide

theorem character_generator_eq : character generator = scalarTwelve := Units.ext character_generator

theorem conjugateCharacter_generator : (conjugateCharacter generator : ZMod 19) = 8 := by
  change (((character generator)⁻¹ : (ZMod 19)ˣ) : ZMod 19) = (8 : ZMod 19)
  rw [character_generator_eq]
  rfl

theorem generator_generates : ∀ u : (ZMod 13)ˣ, ∃ n : Fin 12, u = generator ^ n.val := by decide

theorem character_generator_order : orderOf (character generator) = 6 := by
  apply (orderOf_eq_iff (by decide : 0 < 6)).mpr
  constructor
  · decide
  · intro n hn hn6
    interval_cases n <;> decide

theorem conjugateCharacter_generator_order : orderOf (conjugateCharacter generator) = 6 := by
  change orderOf ((character generator)⁻¹) = 6
  rw [orderOf_inv]
  exact character_generator_order

end MazurTransfer.ThirteenToNineteenCharacterProofHelpers20261018
theorem solution :
    ((character generator : ZMod 19) = 12) ∧
    (character generator = scalarTwelve) ∧
    ((conjugateCharacter generator : ZMod 19) = 8) ∧
    (∀ u : (ZMod 13)ˣ, ∃ n : Fin 12, u = generator ^ n.val) ∧
    (orderOf (character generator) = 6) ∧
    (orderOf (conjugateCharacter generator) = 6) := by
  exact ⟨MazurTransfer.ThirteenToNineteenCharacterProofHelpers20261018.character_generator, MazurTransfer.ThirteenToNineteenCharacterProofHelpers20261018.character_generator_eq, MazurTransfer.ThirteenToNineteenCharacterProofHelpers20261018.conjugateCharacter_generator, MazurTransfer.ThirteenToNineteenCharacterProofHelpers20261018.generator_generates, MazurTransfer.ThirteenToNineteenCharacterProofHelpers20261018.character_generator_order, MazurTransfer.ThirteenToNineteenCharacterProofHelpers20261018.conjugateCharacter_generator_order⟩
#print axioms solution
