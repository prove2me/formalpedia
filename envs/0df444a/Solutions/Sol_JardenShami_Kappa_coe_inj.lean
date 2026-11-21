-- Prove2me | solution 1 for JardenShami.Kappa.coe_inj
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T21:42:35.763285+00:00
-- url     : https://prove2.me/submissions/f452a42a-5b8d-484c-9259-5d8df6df4cfd

import Definitions.Def_MyResearchesLLMLean_JardenShami_Section3
import Mathlib.Data.Sym.Sym2.Order
import Definitions.Def_MyResearchesLLMLean_JardenShami_Section4
import Theorems.Thm_JardenShami_Kappa_coe_le_coe
import Theorems.Thm_JardenShami_Kappa_coe_mk
attribute [local simp] JardenShami.Kappa.coe_mk

set_option autoImplicit true
open Cardinal
universe u v w
noncomputable section
open JardenShami
open Tree
variable {κ : Cardinal.{w}} {D : Type v}
namespace JardenShami
namespace Kappa
theorem _root_.solution {x y : Kappa κ} : (x : Ordinal.{w}) = y ↔ x = y := by
  simp only [le_antisymm_iff, Kappa.coe_le_coe]
end Kappa
end JardenShami
