-- Prove2me | solution 1 for Grunbaum2003.characteristicCone_cone_basics
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T09:49:38.863978+00:00
-- url     : https://prove2.me/submissions/3dcd5f71-0982-4745-a1cb-596cfba65bec

import Definitions.Def_auto_GRUM02ER_1c2100_Grunbaum2003_RecessionDefinitions
import Mathlib.Analysis.Convex.Caratheodory
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Tactic
open Grunbaum2003
open scoped Pointwise

theorem solution {d : ℕ}
    (K : Set (Fin d → ℝ)) :
    Convex ℝ (characteristicCone K) ∧ (0 : Fin d → ℝ) ∈ characteristicCone K ∧
    K + characteristicCone K ⊆ K := by
  constructor
  · intro v hv w hw a b ha hb hab
    intro x hx t ht
    have hm := hw (x+(t*a)•v) (hv x hx (t*a) (mul_nonneg ht ha)) (t*b) (mul_nonneg ht hb)
    convert hm using 1 <;> module
  · constructor
    · intro x hx t ht
      simpa using hx
    · rintro z ⟨x,hx,v,hv,rfl⟩
      simpa using hv x hx 1 (by norm_num)
