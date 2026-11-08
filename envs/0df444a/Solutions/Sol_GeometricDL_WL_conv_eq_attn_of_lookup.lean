-- Prove2me | solution 1 for GeometricDL.WL.conv_eq_attn_of_lookup
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T17:57:26.141861+00:00
-- url     : https://prove2.me/submissions/fecc78b1-5796-49ee-a39d-68351c123bdb

import Mathlib
import Definitions.Def_GeometricDL_WL_convLayer
import Definitions.Def_GeometricDL_WL_attnLayer

open GeometricDL.WL in
theorem solution {V : Type*} [Fintype V] {H M A H' : Type*} [AddCommMonoid M]
    [Module ℝ M] (c : H → H → ℝ) (ψ : H → M) (agg : Multiset M → A) (φ : H → A → H')
    (E : V → V → Prop) [DecidableRel E] (h : V → H) (u : V) :
    convLayer (fun hu hv _ _ => c hu hv) ψ agg φ E h u = attnLayer c ψ agg φ E h u := by
  unfold convLayer attnLayer
  rfl
