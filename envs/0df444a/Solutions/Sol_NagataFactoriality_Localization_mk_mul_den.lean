-- Prove2me | solution 1 for NagataFactoriality.Localization.mk_mul_den
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:51:35.00336+00:00
-- url     : https://prove2.me/submissions/7181c31f-6744-460b-a680-5549457135e6

import Mathlib.RingTheory.Localization.Basic
import Definitions.Def_NagataFactoriality_Localization_MultSet
import Definitions.Def_NagataFactoriality_Localization_Localization

set_option autoImplicit false
open NagataFactoriality
open NagataFactoriality.Localization
variable {α : Type*} [CommRing α] {S : Submonoid α}
namespace NagataFactoriality.Localization
theorem _root_.solution (a s : α) (hs : s ∈ S) :
    mk (S := S) a s hs * of (S := S) s = of (S := S) a := by
  rw [mk, of, _root_.Localization.mk_eq_mk'_apply]
  exact IsLocalization.mk'_spec_mk (M := S) (S := Localization S) a s hs
end NagataFactoriality.Localization
