-- Prove2me | solution 1 for NagataFactoriality.nagata_key_lemma_primeGenerated_isLocalization
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:03:27.378177+00:00
-- url     : https://prove2.me/submissions/98449013-190b-43de-8165-08d0f8281938

import Definitions.Def_NagataFactoriality_Localization_Properties
import Definitions.Def_NagataFactoriality_Localization_IsLocalization
import Definitions.Def_NagataFactoriality_Basic_UFD
import Definitions.Def_NagataFactoriality_Nagata_Lemmas
import Theorems.Thm_NagataFactoriality_prime_of_irreducible_of_dvd_mem_primeGenerated
import Theorems.Thm_NagataFactoriality_localization_irreducible_of_irreducible_primeGenerated_isLocalization
import Theorems.Thm_NagataFactoriality_prime_of_localization_prime_primeGenerated_isLocalization

set_option autoImplicit false
open NagataFactoriality
namespace NagataFactoriality
theorem _root_.solution {α β : Type*}
    [CommRing α] [IsDomain α] {S : Submonoid α} [CommRing β] [Algebra α β] [IsDomain β]
    [_root_.IsLocalization S β] (hS : PrimeGenerated S) [UniqueFactorizationMonoid β]
    {p : α} (hp : Irreducible p) : Prime p := by
  letI : Fact ((0 : α) ∉ S) := ⟨zero_notMem_of_primeGenerated hS⟩
  by_cases hmem : ∃ s : α, s ∈ S ∧ p ∣ s
  · rcases hmem with ⟨s, hs, hdiv⟩
    exact prime_of_irreducible_of_dvd_mem_primeGenerated hS hp hs hdiv
  · have havoid : Avoids S p := by
      intro s hs hdiv
      exact hmem ⟨s, hs, hdiv⟩
    have hlocIrred : Irreducible (algebraMap α β p) :=
      localization_irreducible_of_irreducible_primeGenerated_isLocalization
        (β := β) (S := S) hS hp havoid
    have hlocPrime : Prime (algebraMap α β p) :=
      (UniqueFactorizationMonoid.irreducible_iff_prime).mp hlocIrred
    exact prime_of_localization_prime_primeGenerated_isLocalization
      (β := β) (S := S) hS hp havoid hlocPrime
end NagataFactoriality
