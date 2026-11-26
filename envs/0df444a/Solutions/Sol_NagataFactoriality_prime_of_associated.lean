-- Prove2me | solution 1 for NagataFactoriality.prime_of_associated
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:48:41.032828+00:00
-- url     : https://prove2.me/submissions/82c42a94-a7b5-4cf5-87a8-f6785f2865af

import Mathlib.RingTheory.Noetherian.UniqueFactorizationDomain
import Definitions.Def_NagataFactoriality_Basic_Ring
import Definitions.Def_NagataFactoriality_Basic_Divisibility

set_option autoImplicit false
open NagataFactoriality
open scoped BigOperators
namespace NagataFactoriality
theorem _root_.solution {α : Type*} [CommRing α] [IsDomain α] {p q : α}
    (hp : Prime p) (hassoc : Associated p q) : Prime q := by
  exact (hassoc.prime_iff).mp hp
end NagataFactoriality
