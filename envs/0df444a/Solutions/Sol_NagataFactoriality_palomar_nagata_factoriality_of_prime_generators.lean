-- Prove2me | solution 1 for NagataFactoriality.palomar_nagata_factoriality_of_prime_generators
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:05:52.33092+00:00
-- url     : https://prove2.me/submissions/4a25163c-a933-494f-ad86-41e12fe7820e

import Definitions.Def_NagataFactoriality_Applications_Laurent
import Definitions.Def_NagataFactoriality_Solution
import Theorems.Thm_NagataFactoriality_nagata_theorem_of_prime_generators_isLocalization


set_option autoImplicit false
open NagataFactoriality
open Polynomial
namespace NagataFactoriality
theorem _root_.solution
    {R T : Type*} [CommRing R] [IsDomain R] [IsNoetherianRing R]
    (s : Set R) [CommRing T] [Algebra R T]
    [_root_.IsLocalization (Submonoid.closure s) T] [IsDomain T]
    (hs : ∀ q ∈ s, Prime q) (hUFD : UniqueFactorizationMonoid T) :
    UniqueFactorizationMonoid R := by
  exact nagata_theorem_of_prime_generators_isLocalization
    (R := R) (T := T) s hs hUFD
end NagataFactoriality
