-- Prove2me | solution 1 for NagataFactoriality.isUnit_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:49:40.478037+00:00
-- url     : https://prove2.me/submissions/c6b95dca-60f1-4b4c-a401-6f105fdd1b17

import Mathlib.RingTheory.Noetherian.UniqueFactorizationDomain
import Definitions.Def_NagataFactoriality_Basic_Ring
import Definitions.Def_NagataFactoriality_Basic_Divisibility

set_option autoImplicit false
open NagataFactoriality
open scoped BigOperators
namespace NagataFactoriality
theorem _root_.solution {α : Type*} [CommMonoid α] : IsUnit (1 : α) := ⟨1, rfl⟩
end NagataFactoriality
