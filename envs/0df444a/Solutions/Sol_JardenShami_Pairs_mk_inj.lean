-- Prove2me | solution 1 for JardenShami.Pairs.mk_inj
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T21:42:54.401457+00:00
-- url     : https://prove2.me/submissions/8e93fa3b-0898-4449-833b-55028e00a9f7

import Definitions.Def_MyResearchesLLMLean_JardenShami_Section2
import Definitions.Def_MyResearchesLLMLean_JardenShami_Section3

set_option autoImplicit true
open Cardinal
universe v w
noncomputable section
open JardenShami
namespace JardenShami
namespace Pairs
theorem _root_.solution {A : Type*} [LinearOrder A] {a b c d : A} (hab : a < b) (hcd : c < d)
    (h : Pairs.mk a b hab.ne = Pairs.mk c d hcd.ne) : a = c ∧ b = d := by
  have h' : s(a, b) = s(c, d) := congrArg Subtype.val h
  rcases Sym2.eq_iff.1 h' with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact ⟨h1, h2⟩
  · subst h1; subst h2
    exact absurd (hab.trans hcd) (lt_irrefl _)
end Pairs
end JardenShami
