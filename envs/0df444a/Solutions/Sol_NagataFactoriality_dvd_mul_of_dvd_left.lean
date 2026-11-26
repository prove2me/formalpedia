-- Prove2me | solution 1 for NagataFactoriality.dvd_mul_of_dvd_left
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:49:39.448774+00:00
-- url     : https://prove2.me/submissions/2f2d8191-40b5-4c86-a981-1890a4782d21

import Mathlib.RingTheory.Noetherian.UniqueFactorizationDomain
import Definitions.Def_NagataFactoriality_Basic_Ring
import Definitions.Def_NagataFactoriality_Basic_Divisibility
import Theorems.Thm_NagataFactoriality_dvd_trans

set_option autoImplicit false
open NagataFactoriality
open scoped BigOperators
namespace NagataFactoriality
theorem _root_.solution {α : Type*} [CommMonoid α] {a b c : α} :
    a ∣ b → a ∣ b * c := by
  intro h
  exact dvd_trans h (dvd_mul_right b c)
end NagataFactoriality
