-- Prove2me | solution 2 for NagataFactoriality.Localization.isUnit_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @scuba8684
-- created : 2026-11-26T06:06:39.492128+00:00
-- url     : https://prove2.me/submissions/e4dfa1bf-f1f1-4858-a19e-0bee415f7d8f

import Mathlib.RingTheory.Localization.Basic
import Definitions.Def_NagataFactoriality_Localization_Localization

set_option autoImplicit false

theorem solution {α : Type*} [CommRing α] {S : Submonoid α} {s : α}
    (hs : s ∈ S) : IsUnit (NagataFactoriality.Localization.of (S := S) s) := by
  change IsUnit (algebraMap α (_root_.Localization S) s)
  let denominator : S := ⟨s, hs⟩
  refine isUnit_iff_exists_inv.mpr
    ⟨IsLocalization.mk' (_root_.Localization S) (1 : α) denominator, ?_⟩
  simpa only [map_one] using
    IsLocalization.mk'_spec' (_root_.Localization S) (1 : α) denominator
