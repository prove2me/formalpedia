-- Prove2me | solution 1 for OAI.BufferedIsing.extreme_rectangle
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-14T22:37:18.765862+00:00
-- url     : https://prove2.me/submissions/30bd1e1c-7bb5-4448-aac3-942f7c228727

-- Generated from openai/math@1581d4c lean/OAI/Probability/Ising/Marginals.lean:L61-L79
-- (upload_full_project.md Phase 4): solution for node OAI.BufferedIsing.extreme_rectangle. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` restates it and is proved by it.
import Mathlib
import Definitions.Def_BufferedIsing
import Definitions.Def_OAI_Probability_Ising_Basic
import Definitions.Def_OAI_Probability_Ising_Colorings
import Definitions.Def_OAI_Probability_Ising_EdwardsSokal
import Definitions.Def_OAI_Probability_Ising_TwoSpin
import Definitions.Def_OAI_Probability_Ising_SpinCorrelation
import Definitions.Def_OAI_Probability_Ising_Marginals

-- ---- from OAI.Probability.Ising.Marginals ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

open scoped BigOperators Classical

namespace BufferedIsing

/-- The extreme-rectangle bound does not require the four configurations to be ordered. -/
lemma extreme_rectangle {A B : Type*} [PartialOrder A] [BoundedOrder A]
    [PartialOrder B] [BoundedOrder B] (f : A → B → ℝ)
    (hrect : ∀ u v s t, u ≤ v → s ≤ t → f u t + f v s ≤ f u s + f v t)
    (a a' : A) (b b' : B) :
    |f a b + f a' b' - f a b' - f a' b| ≤
      f ⊤ ⊤ + f ⊥ ⊥ - f ⊤ ⊥ - f ⊥ ⊤ := by
  apply abs_le.mpr
  constructor
  · have h₁ := hrect ⊥ a' ⊥ b' bot_le bot_le
    have h₂ := hrect a ⊤ b ⊤ le_top le_top
    have h₃ := hrect a' ⊤ ⊥ b le_top bot_le
    have h₄ := hrect ⊥ a b' ⊤ bot_le le_top
    linarith
  · have h₁ := hrect ⊥ a' ⊥ b bot_le bot_le
    have h₂ := hrect a ⊤ b' ⊤ le_top le_top
    have h₃ := hrect a' ⊤ ⊥ b' le_top bot_le
    have h₄ := hrect ⊥ a b ⊤ bot_le le_top
    linarith

end BufferedIsing

end OAI

-- ---- platform node ----
open OAI OAI.BufferedIsing
open scoped BigOperators Classical

theorem solution {A B : Type*} [PartialOrder A] [BoundedOrder A]
    [PartialOrder B] [BoundedOrder B] (f : A → B → ℝ)
    (hrect : ∀ u v s t, u ≤ v → s ≤ t → f u t + f v s ≤ f u s + f v t)
    (a a' : A) (b b' : B) :
    |f a b + f a' b' - f a b' - f a' b| ≤
      f ⊤ ⊤ + f ⊥ ⊥ - f ⊤ ⊥ - f ⊥ ⊤ := by
  first
    | exact OAI.BufferedIsing.extreme_rectangle f hrect a a' b b'
    | exact OAI.BufferedIsing.extreme_rectangle
    | (apply OAI.BufferedIsing.extreme_rectangle <;> assumption)
    | (intros; apply OAI.BufferedIsing.extreme_rectangle <;> assumption)
