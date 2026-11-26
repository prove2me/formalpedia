-- Prove2me | solution 1 for NagataFactoriality.Submonoid.zero_notMem_of_prime_or_unit
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:48:21.984985+00:00
-- url     : https://prove2.me/submissions/ca1d50bc-f7aa-4fc7-8581-2bc7bc56524e

import Definitions.Def_NagataFactoriality_Basic_Divisibility
import Definitions.Def_NagataFactoriality_Localization_MultSet

set_option autoImplicit false
open NagataFactoriality
open NagataFactoriality.Submonoid
variable {α : Type*} [CommRing α] [IsDomain α]
namespace NagataFactoriality.Submonoid
theorem _root_.solution {S : Submonoid α}
    (hS : ∀ s ∈ S, Prime s ∨ IsUnit s) : (0 : α) ∉ S := by
  intro h0
  rcases hS 0 h0 with h0prime | h0unit
  · exact h0prime.ne_zero rfl
  · exact h0unit.ne_zero rfl
end NagataFactoriality.Submonoid
