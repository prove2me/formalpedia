-- Prove2me | solution 1 for NagataFactoriality.IsLocalization.isUnit_map_of_isUnit
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:48:44.931916+00:00
-- url     : https://prove2.me/submissions/e26ebf0a-df59-41af-a260-6c9152cbc6a1

import Mathlib.RingTheory.Localization.Basic
import Definitions.Def_NagataFactoriality_Localization_MultSet
import Definitions.Def_NagataFactoriality_Localization_IsLocalization

set_option autoImplicit false
open NagataFactoriality
open NagataFactoriality.IsLocalization
variable {α β : Type*} [CommRing α] [CommRing β] {S : Submonoid α}
variable [Algebra α β] [_root_.IsLocalization S β]
namespace NagataFactoriality.IsLocalization
theorem _root_.solution {a : α} (ha : IsUnit a) : IsUnit (algebraMap α β a) :=
  ha.map (algebraMap α β)
end NagataFactoriality.IsLocalization
