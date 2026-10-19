-- Prove2me | solution 2 for OAI.CriticalZ3.rtg_first_exit
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T20:11:37.538305+00:00
-- url     : https://prove2.me/submissions/c0a4f308-cba0-47fd-ada0-eab0aecb1f30

-- Generated from openai/math@1581d4c lean/OAI/Probability/CriticalZ3/Basic.lean:L571-L586
-- (upload_full_project.md Phase 4): solution for node OAI.CriticalZ3.rtg_first_exit. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_CriticalZ3
import Definitions.Def_OAI_Probability_CriticalZ3_Basic

-- ---- from OAI.Probability.CriticalZ3.Basic ----
-- Lean 4.33 compatibility: Measurable.of_eval is the renamed measurable_pi_lambda
-- (Mathlib/MeasureTheory/MeasurableSpace/Constructions.lean at d13f23b records the alias).
section Lean433MeasurableOfEval
end Lean433MeasurableOfEval

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe uE uOmega uV

-- [generator] trimmed: open MeasureTheory ProbabilityTheory
open _root_.MeasureTheory ProbabilityTheory

namespace CriticalZ3

/-! Finite alterations, tail invariance, and the infinite seed limit. -/

open Filter
open scoped Topology

theorem rtg_first_exit {V : Type uV} {r : V → V → Prop} {D : Set V} {x y : V}
    (h : Relation.ReflTransGen r x y) (hx : x ∈ D) (hy : y ∉ D) :
    ∃ a ∈ D, ∃ b ∉ D, Relation.ReflTransGen (Within D r) x a ∧ r a b := by
  have hh : ∀ {z}, Relation.ReflTransGen r x z →
      (z ∈ D ∧ Relation.ReflTransGen (Within D r) x z) ∨
      ∃ a ∈ D, ∃ b ∉ D, Relation.ReflTransGen (Within D r) x a ∧ r a b := by
    intro z hz
    induction hz with
    | refl => exact Or.inl ⟨hx,.refl⟩
    | @tail a b _ hab ih =>
      rcases ih with ⟨ha,hi⟩ | he
      · by_cases hb : b ∈ D
        · exact Or.inl ⟨hb,hi.tail ⟨ha,hb,hab⟩⟩
        · exact Or.inr ⟨a,ha,b,hb,hi,hab⟩
      · exact Or.inr he
  exact (hh h).resolve_left (fun h => hy h.1)

end CriticalZ3

end OAI

-- ---- platform node ----
open OAI OAI.CriticalZ3
open MeasureTheory ProbabilityTheory
open Filter
open scoped Topology


theorem solution.{uV} : type_of% @_root_.OAI.CriticalZ3.rtg_first_exit.{uV} := @_root_.OAI.CriticalZ3.rtg_first_exit.{uV}
