-- Prove2me | solution 1 for JardenShami.Kappa.coe_mk
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T21:41:39.840372+00:00
-- url     : https://prove2.me/submissions/2e10dd4b-1fd4-496f-ba5c-3b2cae4fa4d5

import Definitions.Def_MyResearchesLLMLean_JardenShami_Section3
import Mathlib.Data.Sym.Sym2.Order
import Definitions.Def_MyResearchesLLMLean_JardenShami_Section4

set_option autoImplicit true
open Cardinal
universe u v w
noncomputable section
open JardenShami
open Tree
variable {κ : Cardinal.{w}} {D : Type v}
namespace JardenShami
namespace Kappa
theorem _root_.solution (α : Ordinal.{w}) (h : α < κ.ord) :
    ((Kappa.mk α h : Kappa κ) : Ordinal.{w}) = α := by
  simp [Kappa.mk]
end Kappa
end JardenShami
