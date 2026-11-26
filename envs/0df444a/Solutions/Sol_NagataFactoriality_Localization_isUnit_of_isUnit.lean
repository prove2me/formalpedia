-- Prove2me | solution 1 for NagataFactoriality.Localization.isUnit_of_isUnit
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:52:31.006328+00:00
-- url     : https://prove2.me/submissions/a3093232-02b8-4718-8e2b-de5405b36130

import Mathlib.RingTheory.Localization.Basic
import Definitions.Def_NagataFactoriality_Localization_MultSet
import Definitions.Def_NagataFactoriality_Localization_Localization

set_option autoImplicit false
open NagataFactoriality
open NagataFactoriality.Localization
variable {α : Type*} [CommRing α] {S : Submonoid α}
namespace NagataFactoriality.Localization
theorem _root_.solution {a : α} (ha : IsUnit a) : IsUnit (of (S := S) a) :=
  ha.map (algebraMap α (Localization S))
end NagataFactoriality.Localization
