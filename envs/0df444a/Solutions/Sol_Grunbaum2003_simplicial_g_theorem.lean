-- Prove2me | solution 1 for Grunbaum2003.simplicial_g_theorem
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-31T22:28:40.1032+00:00
-- url     : https://prove2.me/submissions/f2393208-72c7-41f6-ad25-06dca4607af8
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_Grunbaum2003_IsSimplicialDPolytope
import Definitions.Def_Grunbaum2003_faceCount
import Definitions.Def_Grunbaum2003_IsMSequence
import Definitions.Def_Grunbaum2003_gTheoremMatrix
import Theorems.Thm_Grunbaum2003_gTheoremMatrix_col_zero_sum_and_zero_dim
import Theorems.Thm_Grunbaum2003_simplicial_g_theorem_pos_dim_tail
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic

set_option autoImplicit false
open scoped BigOperators

namespace Grunbaum2003

/-- Full `g`-theorem (Grünbaum 2003, §10.6, pp. 198a–198b): an extended integer `f`-vector
`(f 0, f 1, ..., f d)` is realizable by a simplicial `d`-polytope with `f 0 = 1` iff it equals
`g M_d` for an `M`-sequence `g` of length `⌊d / 2⌋ + 1`. -/
theorem simplicial_g_theorem_sol (d : ℕ) (f : Fin (d + 1) → ℤ) :
    (f 0 = 1 ∧ ∃ P : Set (Fin d → ℝ),
      IsSimplicialDPolytope P ∧
      ∀ j : Fin d, f j.succ = (faceCount P j.val : ℤ)) ↔
    ∃ g : ℕ → ℕ, IsMSequence (d / 2) g ∧
      ∀ k : Fin (d + 1),
        f k = ∑ j ∈ Finset.range (d / 2 + 1),
          (g j : ℤ) * gTheoremMatrix d j k.val := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · exact gTheoremMatrix_col_zero_sum_and_zero_dim.2 f
  · constructor
    · rintro ⟨hf0, hP⟩
      exact (simplicial_g_theorem_pos_dim_tail d hd f hf0).mp hP
    · rintro ⟨g, hg, hfk⟩
      have hf0 : f 0 = 1 := by
        have h0 := hfk 0
        change f 0 = ∑ j ∈ Finset.range (d / 2 + 1), (g j : ℤ) * gTheoremMatrix d j 0 at h0
        rw [gTheoremMatrix_col_zero_sum_and_zero_dim.1 d g, hg.1] at h0
        simpa using h0
      exact ⟨hf0, (simplicial_g_theorem_pos_dim_tail d hd f hf0).mpr ⟨g, hg, hfk⟩⟩

end Grunbaum2003

theorem solution (d : ℕ) (f : Fin (d + 1) → ℤ) :
    (f 0 = 1 ∧ ∃ P : Set (Fin d → ℝ),
      Grunbaum2003.IsSimplicialDPolytope P ∧
      ∀ j : Fin d, f j.succ = (Grunbaum2003.faceCount P j.val : ℤ)) ↔
    ∃ g : ℕ → ℕ, Grunbaum2003.IsMSequence (d / 2) g ∧
      ∀ k : Fin (d + 1),
        f k = ∑ j ∈ Finset.range (d / 2 + 1),
          (g j : ℤ) * Grunbaum2003.gTheoremMatrix d j k.val :=
  Grunbaum2003.simplicial_g_theorem_sol d f
