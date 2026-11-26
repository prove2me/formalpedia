-- Prove2me | solution 1 for NagataFactoriality.dvd_trans
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:47:33.162436+00:00
-- url     : https://prove2.me/submissions/5d740168-58c5-4bc5-88ed-a8fcb312d541

import Mathlib.RingTheory.Noetherian.UniqueFactorizationDomain
import Definitions.Def_NagataFactoriality_Basic_Ring
import Definitions.Def_NagataFactoriality_Basic_Divisibility

set_option autoImplicit false
open NagataFactoriality
open scoped BigOperators
namespace NagataFactoriality
theorem _root_.solution {α : Type*} [CommMonoid α] {a b c : α} :
    a ∣ b → b ∣ c → a ∣ c := by
  intro hab hbc
  exact Dvd.dvd.trans hab hbc
end NagataFactoriality
