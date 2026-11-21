-- Prove2me | solution 1 for JardenShami.IsLocallyAdditive.comp_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T21:45:02.69586+00:00
-- url     : https://prove2.me/submissions/232d3536-13c7-4e89-8cbf-1f97d9b663d3

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
theorem _root_.solution {A : Type w} [LinearOrder A] {D E : Type*}
    {C : Coloring A D} (hC : IsLocallyAdditive C) {ι : D → E} (hι : Function.Injective ι) :
    IsLocallyAdditive (ι ∘ C) := fun a b c d hab hbc hcd h =>
  congrArg ι (hC a b c d hab hbc hcd (hι h))
end IsLocallyAdditive
end JardenShami
