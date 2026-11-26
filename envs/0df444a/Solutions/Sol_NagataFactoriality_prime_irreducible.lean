-- Prove2me | solution 1 for NagataFactoriality.prime_irreducible
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:47:33.659903+00:00
-- url     : https://prove2.me/submissions/759bb5d5-043b-4553-b6de-6a5fcde66275

import Mathlib.RingTheory.Noetherian.UniqueFactorizationDomain
import Definitions.Def_NagataFactoriality_Basic_Ring
import Definitions.Def_NagataFactoriality_Basic_Divisibility

set_option autoImplicit false
open NagataFactoriality
open scoped BigOperators
namespace NagataFactoriality
theorem _root_.solution {α : Type*} [CommRing α] [IsDomain α] {p : α} (hp : Prime p) :
    Irreducible p :=
  hp.irreducible
end NagataFactoriality
