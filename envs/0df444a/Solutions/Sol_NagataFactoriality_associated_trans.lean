-- Prove2me | solution 1 for NagataFactoriality.associated_trans
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:49:45.892584+00:00
-- url     : https://prove2.me/submissions/8c84e80b-da61-44bf-be47-078e30a2e582

import Mathlib.RingTheory.Noetherian.UniqueFactorizationDomain
import Definitions.Def_NagataFactoriality_Basic_Ring
import Definitions.Def_NagataFactoriality_Basic_Divisibility

set_option autoImplicit false
open NagataFactoriality
open scoped BigOperators
namespace NagataFactoriality
theorem _root_.solution {α : Type*} [Monoid α] {a b c : α} :
    Associated a b → Associated b c → Associated a c := fun hab hbc => hab.trans hbc
end NagataFactoriality
