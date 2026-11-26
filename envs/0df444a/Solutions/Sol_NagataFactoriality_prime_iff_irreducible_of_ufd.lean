-- Prove2me | solution 1 for NagataFactoriality.prime_iff_irreducible_of_ufd
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:50:04.367969+00:00
-- url     : https://prove2.me/submissions/00d9f16f-8aed-49a8-bd82-6da948f1aeb4

import Mathlib.RingTheory.UniqueFactorizationDomain.Basic
import Definitions.Def_NagataFactoriality_Basic_Noetherian
import Definitions.Def_NagataFactoriality_Basic_UFD

set_option autoImplicit false
open NagataFactoriality
namespace NagataFactoriality
theorem _root_.solution {α : Type*} [CommRing α] [IsDomain α]
    [UniqueFactorizationMonoid α] {p : α} : Prime p ↔ Irreducible p :=
  UniqueFactorizationMonoid.irreducible_iff_prime.symm
end NagataFactoriality
