-- Prove2me | solution 1 for MIPRE.Introspection.QuestionType.card
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T01:27:29.073006+00:00
-- url     : https://prove2.me/submissions/fe069963-91ab-475a-b16f-b0e503086cb1

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Introspection/Types.lean (solution of MIPRE.Introspection.QuestionType.card);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Tactic.DeriveFintype
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_Introspection_Types

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE.Introspection.AuxType
section
/-- There are exactly `ℓ + 3` auxiliary types for either original player. -/
theorem card (ℓ : ℕ) : Fintype.card (AuxType ℓ) = ℓ + 3 := by
  rw [Fintype.card_congr (equivOption ℓ)]
  simp
end
end MIPRE.Introspection.AuxType

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.Introspection.QuestionType
variable {PauliType : Type*} {ℓ : ℕ}
theorem _root_.solution [Fintype PauliType] (ℓ : ℕ) :
    Fintype.card (QuestionType PauliType ℓ) = Fintype.card PauliType + 2 * ℓ + 6 := by
  simp only [QuestionType, Fintype.card_sum, Fintype.card_prod, Fintype.card_bool, AuxType.card]
  omega
end MIPRE.Introspection.QuestionType
