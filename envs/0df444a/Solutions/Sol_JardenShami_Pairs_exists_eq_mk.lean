-- Prove2me | solution 1 for JardenShami.Pairs.exists_eq_mk
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T21:41:24.332876+00:00
-- url     : https://prove2.me/submissions/f84c3460-9e92-4953-a36c-d711af777ed5

import Definitions.Def_MyResearchesLLMLean_JardenShami_Section2
import Definitions.Def_MyResearchesLLMLean_JardenShami_Section3

set_option autoImplicit true
open Cardinal
universe v w
noncomputable section
open JardenShami
namespace JardenShami
namespace Pairs
theorem _root_.solution {A : Type*} [LinearOrder A] (p : Pairs A) :
    ∃ (a b : A) (h : a < b), p = Pairs.mk a b h.ne := by
  obtain ⟨z, hz⟩ := p
  induction z using Sym2.ind with
  | h x y =>
    have hxy : x ≠ y := by simpa [Sym2.mk_isDiag_iff] using hz
    rcases hxy.lt_or_gt with h | h
    · exact ⟨x, y, h, rfl⟩
    · exact ⟨y, x, h, Subtype.ext Sym2.eq_swap⟩
end Pairs
end JardenShami
