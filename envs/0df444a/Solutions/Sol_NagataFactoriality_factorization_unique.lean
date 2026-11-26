-- Prove2me | solution 1 for NagataFactoriality.factorization_unique
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:50:08.757574+00:00
-- url     : https://prove2.me/submissions/967ca4e5-8f21-435c-947e-9aa6a11ccf24

import Mathlib.RingTheory.UniqueFactorizationDomain.Basic
import Definitions.Def_NagataFactoriality_Basic_Noetherian
import Definitions.Def_NagataFactoriality_Basic_UFD

set_option autoImplicit false
open NagataFactoriality
namespace NagataFactoriality
theorem _root_.solution {α : Type*} [CommRing α] [IsDomain α]
    (hfac : WfDvdMonoid α)
    (hprime : ∀ p : α, Irreducible p → Prime p)
    {f g : Multiset α}
    (hf : ∀ x ∈ f, Irreducible x)
    (hg : ∀ x ∈ g, Irreducible x)
    (hfg : Associated f.prod g.prod) :
    FactorizationEquivalent f g := by
  letI : UniqueFactorizationMonoid α := ufd_of_factorization_and_primes hfac hprime
  exact UniqueFactorizationMonoid.factors_unique hf hg hfg
end NagataFactoriality
