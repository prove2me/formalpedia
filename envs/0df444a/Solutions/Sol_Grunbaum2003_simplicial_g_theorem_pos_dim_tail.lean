-- Prove2me | solution 1 for Grunbaum2003.simplicial_g_theorem_pos_dim_tail
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-02T07:27:58.198666+00:00
-- url     : https://prove2.me/submissions/a57c4358-2588-47a4-8065-b5cfd237ba26
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_Grunbaum2003_IsSimplicialDPolytope
import Definitions.Def_Grunbaum2003_faceCount
import Definitions.Def_Grunbaum2003_IsMSequence
import Definitions.Def_Grunbaum2003_gTheoremMatrix
import Theorems.Thm_Grunbaum2003_simplicial_g_theorem_one_dim
import Theorems.Thm_Grunbaum2003_simplicial_g_theorem_ge_two
import Mathlib.Order.Interval.Finset.Nat

set_option autoImplicit false
open scoped BigOperators

namespace Grunbaum2003

theorem simplicial_g_theorem_pos_dim_tail (d : ℕ) (hd : 0 < d)
    (f : Fin (d + 1) → ℤ) (hf0 : f 0 = 1) :
    (∃ P : Set (Fin d → ℝ),
      IsSimplicialDPolytope P ∧
      ∀ j : Fin d, f j.succ = (faceCount P j.val : ℤ)) ↔
    ∃ g : ℕ → ℕ, IsMSequence (d / 2) g ∧
      ∀ k : Fin (d + 1),
        f k = ∑ j ∈ Finset.range (d / 2 + 1),
          (g j : ℤ) * gTheoremMatrix d j k.val := by
  rcases eq_or_lt_of_le (Nat.succ_le_of_lt hd) with rfl | hd2
  · exact ⟨fun h => (simplicial_g_theorem_one_dim f).mp ⟨hf0, h⟩,
      fun h => ((simplicial_g_theorem_one_dim f).mpr h).2⟩
  · exact simplicial_g_theorem_ge_two d hd2 f hf0

end Grunbaum2003

theorem solution (d : ℕ) (hd : 0 < d)
    (f : Fin (d + 1) → ℤ) (hf0 : f 0 = 1) :
    (∃ P : Set (Fin d → ℝ),
      Grunbaum2003.IsSimplicialDPolytope P ∧
      ∀ j : Fin d, f j.succ = (Grunbaum2003.faceCount P j.val : ℤ)) ↔
    ∃ g : ℕ → ℕ, Grunbaum2003.IsMSequence (d / 2) g ∧
      ∀ k : Fin (d + 1),
        f k = ∑ j ∈ Finset.range (d / 2 + 1),
          (g j : ℤ) * Grunbaum2003.gTheoremMatrix d j k.val :=
  Grunbaum2003.simplicial_g_theorem_pos_dim_tail d hd f hf0
