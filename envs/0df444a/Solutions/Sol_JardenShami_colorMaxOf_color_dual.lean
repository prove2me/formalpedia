-- Prove2me | solution 1 for JardenShami.colorMaxOf_color_dual
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T21:44:49.473711+00:00
-- url     : https://prove2.me/submissions/13aaddc2-aff8-4633-9b7f-fc8c966c2997

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
theorem _root_.solution (f : Kappa κ → Fin 2) (a b : (Kappa κ)ᵒᵈ) (h : a < b) :
    Coloring.color (A := (Kappa κ)ᵒᵈ) (colorMaxOf f) a b h = f (OrderDual.ofDual a) := by
  change f (Sym2.sup s(OrderDual.ofDual a, OrderDual.ofDual b)) = _
  rw [Sym2.sup_mk, sup_of_le_left (show OrderDual.ofDual b ≤ OrderDual.ofDual a from h.le)]
end JardenShami
