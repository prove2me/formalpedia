-- Prove2me | solution 1 for NagataFactoriality.nagata_theorem_of_prime_or_unit_isLocalization
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:03:17.0987+00:00
-- url     : https://prove2.me/submissions/34cd31c3-7ac8-4c4c-815b-38c2e73d5516

import Definitions.Def_NagataFactoriality_Nagata_Lemmas
import Definitions.Def_NagataFactoriality_Nagata_Theorem
import Theorems.Thm_NagataFactoriality_hasFactorization_of_noetherian
import Theorems.Thm_NagataFactoriality_nagata_key_lemma_isLocalization


set_option autoImplicit false
open NagataFactoriality
namespace NagataFactoriality
theorem _root_.solution {R T : Type*}
    [CommRing R] [IsDomain R] [IsNoetherianRing R] (S : Submonoid R) [CommRing T] [Algebra R T]
    [_root_.IsLocalization S T] [IsDomain T]
    (hS : ∀ s ∈ S, Prime s ∨ IsUnit s) (hUFD : UniqueFactorizationMonoid T) :
    UniqueFactorizationMonoid R := by
  letI : UniqueFactorizationMonoid T := hUFD
  exact ufd_of_factorization_and_primes
    (hasFactorization_of_noetherian (α := R))
    (fun p hp => nagata_key_lemma_isLocalization (S := S) (β := T) hS hp)
end NagataFactoriality
