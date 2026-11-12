-- Prove2me | solution 1 for Grunbaum2003.simplicial_g_theorem_ge_two
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-07T19:08:59.417375+00:00
-- url     : https://prove2.me/submissions/9e1442ce-6061-405b-9fd2-12b23687edf9

import Definitions.Def_Grunbaum2003_IsSimplicialDPolytope
import Definitions.Def_Grunbaum2003_faceCount
import Definitions.Def_Grunbaum2003_IsMSequence
import Definitions.Def_Grunbaum2003_gTheoremMatrix
import Theorems.Thm_Grunbaum2003_g_theorem_rhs_low_dim_iff
import Theorems.Thm_Grunbaum2003_simplicial_low_dim_and_higher_g_theorem
import Mathlib.Order.Interval.Finset.Nat
import Lean.Elab.Tactic.Omega

set_option autoImplicit false
open scoped BigOperators

namespace Grunbaum2003

theorem simplicial_g_theorem_ge_two_sol (d : ℕ) (hd : 2 ≤ d)
    (f : Fin (d + 1) → ℤ) (hf0 : f 0 = 1) :
    (∃ P : Set (Fin d → ℝ),
      IsSimplicialDPolytope P ∧
      ∀ j : Fin d, f j.succ = (faceCount P j.val : ℤ)) ↔
    ∃ g : ℕ → ℕ, IsMSequence (d / 2) g ∧
      ∀ k : Fin (d + 1),
        f k = ∑ j ∈ Finset.range (d / 2 + 1),
          (g j : ℤ) * gTheoremMatrix d j k.val := by
  by_cases hd2 : d = 2
  · subst hd2
    have hGeom := simplicial_low_dim_and_higher_g_theorem.1 f hf0
    have hArith := g_theorem_rhs_low_dim_iff.2.2.1 f
    exact ⟨fun h => hArith.mpr ⟨hf0, hGeom.mp h⟩, fun h => hGeom.mpr (hArith.mp h).2⟩
  · by_cases hd3 : d = 3
    · subst hd3
      have hGeom := simplicial_low_dim_and_higher_g_theorem.2.1 f hf0
      have hArith := g_theorem_rhs_low_dim_iff.2.2.2 f
      exact ⟨fun h => hArith.mpr ⟨hf0, hGeom.mp h⟩, fun h => hGeom.mpr (hArith.mp h).2⟩
    · have hd4 : 4 ≤ d := by omega
      exact simplicial_low_dim_and_higher_g_theorem.2.2 d hd4 f hf0

end Grunbaum2003

theorem solution (d : ℕ) (hd : 2 ≤ d)
    (f : Fin (d + 1) → ℤ) (hf0 : f 0 = 1) :
    (∃ P : Set (Fin d → ℝ),
      Grunbaum2003.IsSimplicialDPolytope P ∧
      ∀ j : Fin d, f j.succ = (Grunbaum2003.faceCount P j.val : ℤ)) ↔
    ∃ g : ℕ → ℕ, Grunbaum2003.IsMSequence (d / 2) g ∧
      ∀ k : Fin (d + 1),
        f k = ∑ j ∈ Finset.range (d / 2 + 1),
          (g j : ℤ) * Grunbaum2003.gTheoremMatrix d j k.val :=
  Grunbaum2003.simplicial_g_theorem_ge_two_sol d hd f hf0
