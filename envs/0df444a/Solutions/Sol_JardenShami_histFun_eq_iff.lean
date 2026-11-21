-- Prove2me | solution 1 for JardenShami.histFun_eq_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T21:42:55.526329+00:00
-- url     : https://prove2.me/submissions/fb19fc40-ae89-4278-bdde-1855b603979b

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
theorem _root_.solution {s t : T} : histFun s = histFun t ↔ Set.Iio s = Set.Iio t := by
  simp only [subset_antisymm_iff, histFun_subset_iff]
end JardenShami
