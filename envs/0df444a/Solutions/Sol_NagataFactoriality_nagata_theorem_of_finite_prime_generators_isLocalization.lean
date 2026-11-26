-- Prove2me | solution 1 for NagataFactoriality.nagata_theorem_of_finite_prime_generators_isLocalization
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:05:51.735964+00:00
-- url     : https://prove2.me/submissions/a97f586c-eea3-4794-8a43-e69c2c1dbad8

import Definitions.Def_NagataFactoriality_Nagata_Lemmas
import Definitions.Def_NagataFactoriality_Nagata_Theorem
import Theorems.Thm_NagataFactoriality_nagata_theorem_of_prime_generators_isLocalization

set_option autoImplicit false
open NagataFactoriality
namespace NagataFactoriality
theorem _root_.solution {R T : Type*}
    [CommRing R] [IsDomain R] [IsNoetherianRing R] (s : Finset R) [CommRing T] [Algebra R T]
    [_root_.IsLocalization (Submonoid.closure (↑s : Set R)) T] [IsDomain T]
    (hs : ∀ q ∈ s, Prime q) (hUFD : UniqueFactorizationMonoid T) :
    UniqueFactorizationMonoid R := by
  exact nagata_theorem_of_prime_generators_isLocalization (R := R) (T := T) (s := (↑s : Set R))
    (fun q hq => hs q hq) hUFD
end NagataFactoriality
