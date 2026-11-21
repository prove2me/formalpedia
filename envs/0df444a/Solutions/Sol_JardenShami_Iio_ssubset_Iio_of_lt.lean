-- Prove2me | solution 1 for JardenShami.Iio_ssubset_Iio_of_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T21:44:38.015028+00:00
-- url     : https://prove2.me/submissions/fce406c1-ebf7-4c0c-a265-46b43117ec0c

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
omit [IsTree T]
namespace JardenShami
theorem _root_.solution {u t : T} (h : u < t) : Set.Iio u ⊂ Set.Iio t :=
  ⟨fun _ hx => lt_trans hx h, fun hs => lt_irrefl u (hs h)⟩
end JardenShami
