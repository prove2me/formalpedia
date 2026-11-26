-- Prove2me | solution 1 for NagataFactoriality.dvd_mul_of_dvd_right
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:49:39.94363+00:00
-- url     : https://prove2.me/submissions/1b2c2cea-b077-4b27-857d-73a4d0729194

import Mathlib.RingTheory.Noetherian.UniqueFactorizationDomain
import Definitions.Def_NagataFactoriality_Basic_Ring
import Definitions.Def_NagataFactoriality_Basic_Divisibility
import Theorems.Thm_NagataFactoriality_dvd_trans

set_option autoImplicit false
open NagataFactoriality
open scoped BigOperators
namespace NagataFactoriality
theorem _root_.solution {α : Type*} [CommMonoid α] {a b c : α} :
    a ∣ c → a ∣ b * c := by
  intro h
  exact dvd_trans h (dvd_mul_left c b)
end NagataFactoriality
