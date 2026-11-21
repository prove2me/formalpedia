-- Prove2me | solution 1 for JardenShami.Coloring.color_dual
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T21:45:30.519899+00:00
-- url     : https://prove2.me/submissions/c5b88f22-1154-473c-a633-30fc0515abf7

import Definitions.Def_MyResearchesLLMLean_JardenShami_Section6
import Definitions.Def_MyResearchesLLMLean_JardenShami_Section7

set_option autoImplicit true
open Cardinal
universe v w
noncomputable section
open JardenShami
open Tree
namespace JardenShami
namespace Coloring
theorem _root_.solution {A : Type w} [LinearOrder A] {D : Type v} (C : Coloring A D)
    (a b : Aᵒᵈ) (h : a < b) :
    Coloring.color (A := Aᵒᵈ) C a b h =
      C.color (OrderDual.ofDual b) (OrderDual.ofDual a) h :=
  congrArg C (Subtype.ext Sym2.eq_swap)
end Coloring
end JardenShami
