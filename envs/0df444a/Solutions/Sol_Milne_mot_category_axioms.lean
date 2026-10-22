-- Prove2me | solution 1 for Milne.mot_category_axioms
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T23:11:30.738566+00:00
-- url     : https://prove2.me/submissions/8cb13392-a8e6-4e02-86dd-208b8b5413b1

import Mathlib
import Definitions.Def_Milne_world
import Definitions.Def_Milne_motives
import Definitions.Def_Milne_zeta
universe u v

open Milne

theorem solution (W : CorrWorld.{u, v}) (M N P Q : MotElem W)
    (f : Hom W M N) (g : Hom W N P) (h : Hom W P Q) :
    homComp W (homComp W f g) h = homComp W f (homComp W g h)
      ∧ homComp W (idM W M) f = f
      ∧ homComp W f (idM W N) = f := by
  obtain ⟨γ, hγ, hd⟩ := f
  refine ⟨Subtype.ext ?_, Subtype.ext ?_, Subtype.ext ?_⟩
  · exact W.cc_assoc γ g.val h.val
  · show W.cc M.e γ = γ
    have h1 : W.cc M.e γ = W.cc M.e (W.cc (W.cc M.e γ) N.e) := by rw [hγ]
    rw [h1, ← W.cc_assoc, ← W.cc_assoc, M.idem, hγ]
  · show W.cc γ N.e = γ
    have h1 : W.cc γ N.e = W.cc (W.cc (W.cc M.e γ) N.e) N.e := by rw [hγ]
    rw [h1, W.cc_assoc, N.idem, hγ]
