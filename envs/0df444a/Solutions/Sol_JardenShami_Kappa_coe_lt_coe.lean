-- Prove2me | solution 1 for JardenShami.Kappa.coe_lt_coe
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T21:41:42.654771+00:00
-- url     : https://prove2.me/submissions/dcdf9ad4-a2a0-4b90-a21c-4714166653dc

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
theorem _root_.solution {x y : Kappa κ} : (x : Ordinal.{w}) < y ↔ x < y :=
  Subtype.coe_lt_coe.trans Ordinal.ToType.mk.symm.lt_iff_lt
end Kappa
end JardenShami
