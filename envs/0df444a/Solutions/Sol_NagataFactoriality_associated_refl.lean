-- Prove2me | solution 1 for NagataFactoriality.associated_refl
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:49:42.796803+00:00
-- url     : https://prove2.me/submissions/e1a14dce-22ac-45d6-ba44-cbbc4e57ea37

import Mathlib.RingTheory.Noetherian.UniqueFactorizationDomain
import Definitions.Def_NagataFactoriality_Basic_Ring
import Definitions.Def_NagataFactoriality_Basic_Divisibility

set_option autoImplicit false
open NagataFactoriality
open scoped BigOperators
namespace NagataFactoriality
theorem _root_.solution {α : Type*} [Monoid α] (a : α) : Associated a a := Associated.refl a
end NagataFactoriality
