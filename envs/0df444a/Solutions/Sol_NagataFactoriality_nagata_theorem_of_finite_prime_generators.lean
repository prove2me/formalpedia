-- Prove2me | solution 1 for NagataFactoriality.nagata_theorem_of_finite_prime_generators
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:06:02.662919+00:00
-- url     : https://prove2.me/submissions/925e8bba-fbdc-4b81-8a28-bc3a7b30fd7a

import Definitions.Def_NagataFactoriality_Nagata_Lemmas
import Definitions.Def_NagataFactoriality_Nagata_Theorem
import Theorems.Thm_NagataFactoriality_nagata_theorem_of_prime_generators
import Theorems.Thm_NagataFactoriality_primeGenerated_closure_finset_of_primes


set_option autoImplicit false
open NagataFactoriality
namespace NagataFactoriality
theorem _root_.solution {R : Type*} [CommRing R] [IsDomain R]
    [IsNoetherianRing R] (s : Finset R) (hs : ∀ q ∈ s, Prime q)
    (hUFD :
      @UniqueFactorizationMonoid (Localization (Submonoid.closure (↑s : Set R)))
        (by
          let hS : PrimeGenerated (Submonoid.closure (↑s : Set R)) :=
            primeGenerated_closure_finset_of_primes s hs
          letI : Fact ((0 : R) ∉ Submonoid.closure (↑s : Set R)) :=
            ⟨zero_notMem_of_primeGenerated hS⟩
          infer_instance)) :
    UniqueFactorizationMonoid R := by
  exact nagata_theorem_of_prime_generators (R := R) (s := (↑s : Set R)) (fun q hq => hs q hq) hUFD
end NagataFactoriality
