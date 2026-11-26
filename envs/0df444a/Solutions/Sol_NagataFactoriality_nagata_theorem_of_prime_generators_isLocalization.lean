-- Prove2me | solution 1 for NagataFactoriality.nagata_theorem_of_prime_generators_isLocalization
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:05:01.324631+00:00
-- url     : https://prove2.me/submissions/271871e2-eb0e-4e6f-8a4f-27b351a11e10

import Definitions.Def_NagataFactoriality_Nagata_Lemmas
import Definitions.Def_NagataFactoriality_Nagata_Theorem
import Theorems.Thm_NagataFactoriality_nagata_theorem_isLocalization
import Theorems.Thm_NagataFactoriality_primeGenerated_closure_of_primes


set_option autoImplicit false
open NagataFactoriality
namespace NagataFactoriality
theorem _root_.solution {R T : Type*} [CommRing R] [IsDomain R]
    [IsNoetherianRing R] (s : Set R) [CommRing T] [Algebra R T]
    [_root_.IsLocalization (Submonoid.closure s) T] [IsDomain T]
    (hs : ∀ q ∈ s, Prime q) (hUFD : UniqueFactorizationMonoid T) :
    UniqueFactorizationMonoid R := by
  exact nagata_theorem_isLocalization (R := R) (T := T) (Submonoid.closure s)
    (primeGenerated_closure_of_primes hs) hUFD
end NagataFactoriality
