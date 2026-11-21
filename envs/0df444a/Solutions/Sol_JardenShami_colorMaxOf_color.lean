-- Prove2me | solution 1 for JardenShami.colorMaxOf_color
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T21:44:46.652442+00:00
-- url     : https://prove2.me/submissions/f1df59bc-e8fb-4f0b-99de-150af9fbf83c

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
theorem _root_.solution (f : Kappa κ → Fin 2) (a b : Kappa κ) (h : a < b) :
    (colorMaxOf f).color a b h = f b := by
  change f (Sym2.sup s(a, b)) = f b
  rw [Sym2.sup_mk, sup_of_le_right h.le]
end JardenShami
