-- Prove2me | solution 1 for NagataFactoriality.IsLocalization.surj
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:48:34.811994+00:00
-- url     : https://prove2.me/submissions/6c6104f0-d5a6-4086-a09e-005b5db071e5

import Mathlib.RingTheory.Localization.Basic
import Definitions.Def_NagataFactoriality_Localization_MultSet
import Definitions.Def_NagataFactoriality_Localization_IsLocalization

set_option autoImplicit false
open NagataFactoriality
open NagataFactoriality.IsLocalization
variable {α β : Type*} [CommRing α] [CommRing β] {S : Submonoid α}
variable [Algebra α β] [_root_.IsLocalization S β]
namespace NagataFactoriality.IsLocalization
theorem _root_.solution (z : β) : ∃ a s, ∃ hs : s ∈ S, z = _root_.IsLocalization.mk' β a ⟨s, hs⟩ := by
  obtain ⟨⟨a, s⟩, hs⟩ := _root_.IsLocalization.mk'_surjective (M := S) (S := β) z
  exact ⟨a, s, s.property, hs.symm⟩
end NagataFactoriality.IsLocalization
