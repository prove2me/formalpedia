-- Prove2me | solution 1 for NagataFactoriality.factorizationEquivalent_iff_map_eq_map
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:50:08.023018+00:00
-- url     : https://prove2.me/submissions/bf168b48-3fee-4319-8f3b-f9aee0f50290

import Mathlib.RingTheory.UniqueFactorizationDomain.Basic
import Definitions.Def_NagataFactoriality_Basic_Noetherian
import Definitions.Def_NagataFactoriality_Basic_UFD

set_option autoImplicit false
open NagataFactoriality
namespace NagataFactoriality
theorem _root_.solution {α : Type*} [CommMonoid α] {f g : Multiset α} :
    FactorizationEquivalent f g ↔ f.map Associates.mk = g.map Associates.mk :=
  Associates.rel_associated_iff_map_eq_map
end NagataFactoriality
