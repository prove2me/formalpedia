-- Prove2me | solution 1 for JardenShami.mem_fiberRestr
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T21:42:36.6715+00:00
-- url     : https://prove2.me/submissions/e95bab02-dcdd-4c39-8c94-0916d0931413

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
theorem _root_.solution {C : Coloring (Kappa κ) D} {δ β : Kappa κ} {hβ : β ≤ δ}
    {α : Kappa κ} {d : D} :
    (α, d) ∈ fiberRestr C δ β hβ ↔ ∃ h : α < β, d = C.color α δ (h.trans_le hβ) :=
  Iff.rfl
end JardenShami
