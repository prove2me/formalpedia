-- Prove2me | solution 1 for GeomDL.Blueprint.act_linear
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung
-- created : 2026-10-21T19:33:54.493634+00:00
-- url     : https://prove2.me/submissions/6931edd8-70b8-4de7-af9a-84f60a908692

import Mathlib
import Definitions.Def_GeomDL_Blueprint_Defs

open GeomDL.Blueprint

theorem solution {G Ω : Type*} [Group G] [MulAction G Ω]
    (g : G) (α β : ℝ) (x x' : Ω → ℝ) :
    act g (α • x + β • x') = α • act g x + β • act g x' := by
  funext u
  simp [act]
