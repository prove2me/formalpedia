-- Prove2me | solution 1 for NagataFactoriality.nagata_theorem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:04:14.986837+00:00
-- url     : https://prove2.me/submissions/0d1358e4-1775-4251-959a-4511007ee297

import Definitions.Def_NagataFactoriality_Nagata_Lemmas
import Definitions.Def_NagataFactoriality_Nagata_Theorem
import Theorems.Thm_NagataFactoriality_hasFactorization_of_noetherian
import Theorems.Thm_NagataFactoriality_nagata_key_lemma_primeGenerated_isLocalization


set_option autoImplicit false
open NagataFactoriality
namespace NagataFactoriality
theorem _root_.solution {R : Type*} [CommRing R] [IsDomain R] [IsNoetherianRing R]
    (S : Submonoid R) (hS : PrimeGenerated S)
    (hUFD :
      @UniqueFactorizationMonoid (Localization S)
        (by
          letI : Fact ((0 : R) ∉ S) := ⟨zero_notMem_of_primeGenerated hS⟩
          infer_instance)) :
    UniqueFactorizationMonoid R := by
  letI : Fact ((0 : R) ∉ S) := ⟨zero_notMem_of_primeGenerated hS⟩
  letI : UniqueFactorizationMonoid (Localization S) := hUFD
  exact ufd_of_factorization_and_primes
    (hasFactorization_of_noetherian (α := R))
    (fun p hp => nagata_key_lemma_primeGenerated_isLocalization
      (S := S) (β := Localization S) hS hp)
end NagataFactoriality
