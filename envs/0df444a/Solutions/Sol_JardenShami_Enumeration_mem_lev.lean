-- Prove2me | solution 1 for JardenShami.Enumeration.mem_lev
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T21:44:50.588388+00:00
-- url     : https://prove2.me/submissions/dc44e49e-4630-44de-af83-4d07033fda97

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
theorem _root_.solution (e : Enumeration κ T) {α i : Ordinal.{w}} (hα : α < κ.ord)
    (hi : i < (#(Lev T α)).ord) : e.t α i ∈ Lev T α :=
  (e.bijOn α hα).mapsTo hi
end Enumeration
end JardenShami
