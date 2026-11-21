-- Prove2me | solution 1 for JardenShami.Pairs.map_mk
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T21:44:29.354188+00:00
-- url     : https://prove2.me/submissions/301bbd22-543e-4786-84bc-0c73a157ffc3

import Definitions.Def_MyResearchesLLMLean_JardenShami_Section2
import Definitions.Def_MyResearchesLLMLean_JardenShami_Section3

set_option autoImplicit true
open Cardinal
universe v w
noncomputable section
open JardenShami
namespace JardenShami
namespace Pairs
theorem _root_.solution {A B : Type*} (f : A → B) (hf : Function.Injective f) (a b : A)
    (h : a ≠ b) : Pairs.map f hf (Pairs.mk a b h) = Pairs.mk (f a) (f b) (hf.ne h) :=
  Subtype.ext (Sym2.map_mk f a b)
end Pairs
end JardenShami
