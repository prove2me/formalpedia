-- Prove2me | solution 1 for NagataFactoriality.prime_of_irreducible_of_dvd_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:00:46.075993+00:00
-- url     : https://prove2.me/submissions/1664d2ce-ff1c-43f8-809c-cf30595ebbb1

import Definitions.Def_NagataFactoriality_Localization_Properties
import Definitions.Def_NagataFactoriality_Localization_IsLocalization
import Definitions.Def_NagataFactoriality_Basic_UFD
import Definitions.Def_NagataFactoriality_Nagata_Lemmas
import Theorems.Thm_NagataFactoriality_associated_of_irreducible_of_dvd
import Theorems.Thm_NagataFactoriality_associated_symm
import Theorems.Thm_NagataFactoriality_prime_irreducible
import Theorems.Thm_NagataFactoriality_prime_of_associated


set_option autoImplicit false
open NagataFactoriality
namespace NagataFactoriality
theorem _root_.solution {α : Type*} [CommRing α] [IsDomain α] {S : Submonoid α}
    (hS : ∀ s ∈ S, Prime s ∨ IsUnit s) {p s : α}
    (hp : Irreducible p) (hs : s ∈ S) (hdiv : p ∣ s) : Prime p := by
  rcases hS s hs with hsPrime | hsUnit
  · have hsIrred : Irreducible s := prime_irreducible hsPrime
    have hassoc : Associated p s := associated_of_irreducible_of_dvd hp hsIrred hdiv
    exact prime_of_associated hsPrime (associated_symm hassoc)
  · exact False.elim (hp.not_isUnit (isUnit_of_dvd_unit hdiv hsUnit))
end NagataFactoriality
