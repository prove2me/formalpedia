-- Prove2me | solution 1 for JardenShami.IsLocallyAdditive.color_eq_of_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T21:45:01.441181+00:00
-- url     : https://prove2.me/submissions/72bb89ca-897d-4391-9984-4d0f045a8e11

import Definitions.Def_MyResearchesLLMLean_JardenShami_Section4
import Mathlib.SetTheory.Cardinal.Pigeonhole
import Definitions.Def_MyResearchesLLMLean_JardenShami_Section5

set_option autoImplicit true
open Cardinal
universe w
noncomputable section
open JardenShami
open Tree
variable {κ : Cardinal.{w}}
namespace JardenShami
namespace IsLocallyAdditive
theorem _root_.solution {A : Type w} [LinearOrder A] {D : Type*}
    {C : Coloring A D} (hC : IsLocallyAdditive C) {a δ δ' α : A} (ha : a < δ) (ha' : a < δ')
    (h : C.color a δ ha = C.color a δ' ha') (hα : α ≤ a) :
    C.color α δ (hα.trans_lt ha) = C.color α δ' (hα.trans_lt ha') := by
  rcases hα.lt_or_eq with hα | rfl
  · rcases lt_trichotomy δ δ' with hd | rfl | hd
    · exact hC α a δ δ' hα ha hd h
    · rfl
    · exact (hC α a δ' δ hα ha' hd h.symm).symm
  · exact h
end IsLocallyAdditive
end JardenShami
