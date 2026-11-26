-- Prove2me | solution 1 for NagataFactoriality.IsNoetherianRing.hasFactorization
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:50:00.928318+00:00
-- url     : https://prove2.me/submissions/90f2c0c5-1463-44d1-b712-0ad7d1b5526a

import Mathlib.RingTheory.Noetherian.UniqueFactorizationDomain
import Definitions.Def_NagataFactoriality_Basic_Divisibility
import Definitions.Def_NagataFactoriality_Basic_Noetherian
import Theorems.Thm_NagataFactoriality_hasFactorization_of_noetherian

set_option autoImplicit false
open NagataFactoriality
namespace NagataFactoriality
namespace IsNoetherianRing
theorem _root_.solution {α : Type*} [CommRing α] [IsDomain α]
    (h : IsNoetherianRing α) : WfDvdMonoid α := by
  letI := h
  exact hasFactorization_of_noetherian (α := α)
end IsNoetherianRing
end NagataFactoriality
