-- Prove2me | solution 1 for JardenShami.mem_histFun
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T21:45:49.724405+00:00
-- url     : https://prove2.me/submissions/b528f131-2726-4152-8f6c-0d1962225581

import Definitions.Def_MyResearchesLLMLean_JardenShami_Section3
import Mathlib.Data.Sym.Sym2.Order
import Definitions.Def_MyResearchesLLMLean_JardenShami_Section4

set_option autoImplicit true
open Cardinal
universe u v w
noncomputable section
open JardenShami
open Tree
variable {T : Type w} [PartialOrder T] [IsTree T]
namespace JardenShami
theorem _root_.solution {s p : T} {α : Ordinal.{w}} : (α, p) ∈ histFun s ↔ p < s ∧ ht p = α :=
  Iff.rfl
end JardenShami
