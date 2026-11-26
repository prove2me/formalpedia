-- Prove2me | solution 1 for NagataFactoriality.ufd_of_factorization_and_prime_irreducibles
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:03:19.092871+00:00
-- url     : https://prove2.me/submissions/ec666b27-cbc7-460c-83d8-dea493d5df50

import Definitions.Def_NagataFactoriality_Nagata_Lemmas
import Definitions.Def_NagataFactoriality_Nagata_Theorem

set_option autoImplicit false
open NagataFactoriality
namespace NagataFactoriality
theorem _root_.solution {α : Type*} [CommRing α] [IsDomain α]
    (hfac : WfDvdMonoid α)
    (hprime : ∀ p : α, Irreducible p → Prime p) :
    UniqueFactorizationMonoid α :=
  ufd_of_factorization_and_primes hfac hprime
end NagataFactoriality
