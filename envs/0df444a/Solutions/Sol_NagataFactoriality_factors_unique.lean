-- Prove2me | solution 1 for NagataFactoriality.factors_unique
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:50:09.94023+00:00
-- url     : https://prove2.me/submissions/ebdf4033-ec9b-4922-a8e5-a2d858ccbf9d

import Mathlib.RingTheory.UniqueFactorizationDomain.Basic
import Definitions.Def_NagataFactoriality_Basic_Noetherian
import Definitions.Def_NagataFactoriality_Basic_UFD

set_option autoImplicit false
open NagataFactoriality
namespace NagataFactoriality
theorem _root_.solution {α : Type*} [CommRing α] [IsDomain α]
    (hfac : WfDvdMonoid α)
    (hprime : ∀ p : α, Irreducible p → Prime p)
    {a : α} (ha : a ≠ 0) {f : Multiset α}
    (hf : ∀ x ∈ f, Irreducible x)
    (hfa : Associated f.prod a) :
    letI : UniqueFactorizationMonoid α := ufd_of_factorization_and_primes hfac hprime
    FactorizationEquivalent f (UniqueFactorizationMonoid.factors a) := by
  letI : UniqueFactorizationMonoid α := ufd_of_factorization_and_primes hfac hprime
  exact UniqueFactorizationMonoid.factors_unique hf UniqueFactorizationMonoid.irreducible_of_factor
    (hfa.trans (UniqueFactorizationMonoid.factors_prod ha).symm)
end NagataFactoriality
