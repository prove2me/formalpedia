-- Prove2me | solution 1 for OAI.CriticalZ3.rtg_first_exit
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T19:32:58.676267+00:00
-- url     : https://prove2.me/submissions/eaca79ef-253f-4566-8791-ca0aa4ccbb17

import Mathlib
import Definitions.Def_CriticalZ3
import Definitions.Def_OAI_Probability_CriticalZ3_Basic

open OAI OAI.CriticalZ3
universe uE uOmega uV
open MeasureTheory ProbabilityTheory
open Filter
open scoped Topology


theorem solution {V : Type uV} {r : V → V → Prop} {D : Set V} {x y : V}
    (h : Relation.ReflTransGen r x y) (hx : x ∈ D) (hy : y ∉ D) :
    ∃ a ∈ D, ∃ b ∉ D, Relation.ReflTransGen (Within D r) x a ∧ r a b := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact absurd hx hy
  | head hxz hzy ih =>
    rename_i x' z
    by_cases hz : z ∈ D
    · obtain ⟨a, ha, b, hb, hza, hab⟩ := ih hz
      exact ⟨a, ha, b, hb, Relation.ReflTransGen.head ⟨hx, hz, hxz⟩ hza, hab⟩
    · exact ⟨x', hx, z, hz, Relation.ReflTransGen.refl, hxz⟩

