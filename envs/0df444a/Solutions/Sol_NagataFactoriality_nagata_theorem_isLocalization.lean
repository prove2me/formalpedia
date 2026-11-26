-- Prove2me | solution 1 for NagataFactoriality.nagata_theorem_isLocalization
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:04:14.505495+00:00
-- url     : https://prove2.me/submissions/c74c78fc-ab48-4db4-b896-446667393d44

import Definitions.Def_NagataFactoriality_Nagata_Lemmas
import Definitions.Def_NagataFactoriality_Nagata_Theorem
import Theorems.Thm_NagataFactoriality_hasFactorization_of_noetherian
import Theorems.Thm_NagataFactoriality_nagata_key_lemma_primeGenerated_isLocalization


set_option autoImplicit false
open NagataFactoriality
namespace NagataFactoriality
theorem _root_.solution {R T : Type*} [CommRing R] [IsDomain R] [IsNoetherianRing R]
    (S : Submonoid R) [CommRing T] [Algebra R T] [_root_.IsLocalization S T]
    [IsDomain T] (hS : PrimeGenerated S) (hUFD : UniqueFactorizationMonoid T) :
    UniqueFactorizationMonoid R := by
  letI : UniqueFactorizationMonoid T := hUFD
  exact ufd_of_factorization_and_primes
    (hasFactorization_of_noetherian (α := R))
    (fun p hp => nagata_key_lemma_primeGenerated_isLocalization (S := S) (β := T) hS hp)
end NagataFactoriality
