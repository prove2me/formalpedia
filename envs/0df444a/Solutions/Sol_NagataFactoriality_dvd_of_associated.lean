-- Prove2me | solution 1 for NagataFactoriality.dvd_of_associated
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:48:36.741494+00:00
-- url     : https://prove2.me/submissions/f96a11cc-3eb1-416e-82db-fd421e33c939

import Mathlib.RingTheory.Noetherian.UniqueFactorizationDomain
import Definitions.Def_NagataFactoriality_Basic_Ring
import Definitions.Def_NagataFactoriality_Basic_Divisibility

set_option autoImplicit false
open NagataFactoriality
open scoped BigOperators
namespace NagataFactoriality
theorem _root_.solution {α : Type*} [Monoid α] {a b : α} (h : Associated a b) : a ∣ b :=
  h.dvd
end NagataFactoriality
