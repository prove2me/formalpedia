-- Prove2me | solution 1 for JardenShami.Kappa.coe_le_coe
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T21:41:45.483423+00:00
-- url     : https://prove2.me/submissions/d59b769d-fcd4-448f-abf1-69f19f693439

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
theorem _root_.solution {x y : Kappa κ} : (x : Ordinal.{w}) ≤ y ↔ x ≤ y :=
  Subtype.coe_le_coe.trans Ordinal.ToType.mk.symm.le_iff_le
end Kappa
end JardenShami
