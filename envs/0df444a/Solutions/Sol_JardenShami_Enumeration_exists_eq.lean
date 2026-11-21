-- Prove2me | solution 1 for JardenShami.Enumeration.exists_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T21:43:36.838494+00:00
-- url     : https://prove2.me/submissions/b870aff7-3b90-4761-bbbc-fff16eaf4c22

import Definitions.Def_MyResearchesLLMLean_JardenShami_Section3
import Mathlib.Data.Sym.Sym2.Order
import Definitions.Def_MyResearchesLLMLean_JardenShami_Section4

set_option autoImplicit true
open Cardinal
universe u v w
noncomputable section
open JardenShami
open Tree
variable {κ : Cardinal.{w}} {T : Type w} [PartialOrder T] [IsTree T]
namespace JardenShami
namespace Enumeration
theorem _root_.solution (e : Enumeration κ T) {α : Ordinal.{w}} (hα : α < κ.ord) {x : T}
    (hx : x ∈ Lev T α) : ∃ i < (#(Lev T α)).ord, e.t α i = x :=
  (e.bijOn α hα).surjOn hx
end Enumeration
end JardenShami
