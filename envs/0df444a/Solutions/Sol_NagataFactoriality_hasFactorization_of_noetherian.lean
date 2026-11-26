-- Prove2me | solution 1 for NagataFactoriality.hasFactorization_of_noetherian
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:48:01.363103+00:00
-- url     : https://prove2.me/submissions/5d8faa1f-49c4-4679-87e0-dc5e2ea1beb4

import Mathlib.RingTheory.Noetherian.UniqueFactorizationDomain
import Definitions.Def_NagataFactoriality_Basic_Divisibility
import Definitions.Def_NagataFactoriality_Basic_Noetherian

set_option autoImplicit false
open NagataFactoriality
namespace NagataFactoriality
theorem _root_.solution {α : Type*} [CommRing α] [IsDomain α]
    [IsNoetherianRing α] : WfDvdMonoid α := by
  infer_instance
end NagataFactoriality
