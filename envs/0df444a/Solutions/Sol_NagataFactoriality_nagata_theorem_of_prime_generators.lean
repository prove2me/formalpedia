-- Prove2me | solution 1 for NagataFactoriality.nagata_theorem_of_prime_generators
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:05:02.378994+00:00
-- url     : https://prove2.me/submissions/0973e5d0-b9a0-4070-97fb-d1b144c12aba

import Definitions.Def_NagataFactoriality_Nagata_Lemmas
import Definitions.Def_NagataFactoriality_Nagata_Theorem
import Theorems.Thm_NagataFactoriality_nagata_theorem
import Theorems.Thm_NagataFactoriality_primeGenerated_closure_of_primes


set_option autoImplicit false
open NagataFactoriality
namespace NagataFactoriality
theorem _root_.solution {R : Type*} [CommRing R] [IsDomain R]
    [IsNoetherianRing R] (s : Set R) (hs : ∀ q ∈ s, Prime q)
    (hUFD :
      @UniqueFactorizationMonoid (Localization (Submonoid.closure s))
        (by
          let hS : PrimeGenerated (Submonoid.closure s) := primeGenerated_closure_of_primes hs
          letI : Fact ((0 : R) ∉ Submonoid.closure s) := ⟨zero_notMem_of_primeGenerated hS⟩
          infer_instance)) :
    UniqueFactorizationMonoid R := by
  exact nagata_theorem (R := R) (Submonoid.closure s) (primeGenerated_closure_of_primes hs) hUFD
end NagataFactoriality
