-- Prove2me | solution 1 for GeomDL.Blueprint.eq_3_action
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-21T19:36:34.190173+00:00
-- url     : https://prove2.me/submissions/357819b8-8f95-4b36-baac-576fb98c3494

import Mathlib
import Definitions.Def_GeomDL_Blueprint_Defs

open GeomDL.Blueprint

theorem solution {G Ω C : Type*} [Group G] [MulAction G Ω] :
    (∀ (g h : G) (x : Ω → C), act g (act h x) = act (g * h) x) ∧
    (∀ x : Ω → C, act (1 : G) x = x) := by
  refine ⟨fun g h x => ?_, fun x => ?_⟩
  · funext u; simp [act, mul_smul]
  · funext u; simp [act]
