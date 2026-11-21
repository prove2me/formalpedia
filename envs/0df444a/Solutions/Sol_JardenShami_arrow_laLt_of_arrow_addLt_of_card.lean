-- Prove2me | solution 1 for JardenShami.arrow_laLt_of_arrow_addLt_of_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T21:46:08.849188+00:00
-- url     : https://prove2.me/submissions/1696ec91-7dce-4804-8cb3-978576637f7b

import Definitions.Def_MyResearchesLLMLean_JardenShami_Section2
import Definitions.Def_MyResearchesLLMLean_JardenShami_Section3
import Theorems.Thm_JardenShami_arrow_la_of_arrow_add_of_card

set_option autoImplicit true
open Cardinal
universe v w
noncomputable section
open JardenShami
variable {X : Type w} [LinearOrder X]
namespace JardenShami
theorem _root_.solution (μ : Cardinal.{v})
    (hpow : ∀ D : Type v, #D < μ → #(D → Option D) < μ) (F : Set (Set X))
    (h : Arrow F F (addLt μ)) : Arrow F F (laLt μ) :=
  arrow_la_of_arrow_add_of_card (· < μ) (· < μ) (fun D hD => ⟨hD, hpow D hD⟩) F h
end JardenShami
