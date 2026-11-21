-- Prove2me | solution 1 for JardenShami.Enumeration.ht_t
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T21:45:28.124604+00:00
-- url     : https://prove2.me/submissions/977f4719-5e33-48a5-ab74-98a5b30fcaba

import Definitions.Def_MyResearchesLLMLean_JardenShami_Section3
import Mathlib.Data.Sym.Sym2.Order
import Definitions.Def_MyResearchesLLMLean_JardenShami_Section4
import Theorems.Thm_JardenShami_Enumeration_mem_lev

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
    (hi : i < (#(Lev T α)).ord) : ht (e.t α i) = α :=
  e.mem_lev hα hi
end Enumeration
end JardenShami
