-- Prove2me | solution 1 for NagataFactoriality.associated_symm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:48:14.898947+00:00
-- url     : https://prove2.me/submissions/d842438c-c32a-43b9-a1af-483ba2d589ca

import Mathlib.RingTheory.Noetherian.UniqueFactorizationDomain
import Definitions.Def_NagataFactoriality_Basic_Ring
import Definitions.Def_NagataFactoriality_Basic_Divisibility

set_option autoImplicit false
open NagataFactoriality
open scoped BigOperators
namespace NagataFactoriality
theorem _root_.solution {α : Type*} [Monoid α] {a b : α} :
    Associated a b → Associated b a := Associated.symm
end NagataFactoriality
