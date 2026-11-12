-- Prove2me | solution 1 for Grunbaum2003.g_theorem_necessity_nonstacked
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-09T02:38:50.953095+00:00
-- url     : https://prove2.me/submissions/cef19ec2-affd-471b-9640-b41918ff9e28

import Definitions.Def_Grunbaum2003_IsSimplicialDPolytope
import Definitions.Def_Grunbaum2003_faceCount
import Definitions.Def_Grunbaum2003_IsMSequence
import Definitions.Def_Grunbaum2003_gTheoremMatrix
import Theorems.Thm_Grunbaum2003_gTheoremMatrix_upper_triangular_and_nonstacked_g2
import Theorems.Thm_Grunbaum2003_g_theorem_necessity_nonstacked_pos_g2
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Order.Interval.Finset.Nat

set_option autoImplicit false
open scoped BigOperators

open Grunbaum2003

theorem solution (d : ℕ) (hd : 4 ≤ d) (P : Set (Fin d → ℝ))
    (hP : IsSimplicialDPolytope P) (hV_gt : d + 1 < faceCount P 0)
    (hNonStacked : ¬ ∀ j : Fin d, (faceCount P j.val : ℤ) =
      (Nat.choose (d + 1) j.succ.val : ℤ) +
        ((faceCount P 0 - (d + 1) : ℕ) : ℤ) * gTheoremMatrix d 1 j.succ.val) :
    ∃ g : ℕ → ℕ, IsMSequence (d / 2) g ∧
      ∀ j : Fin d, (faceCount P j.val : ℤ) =
        ∑ i ∈ Finset.range (d / 2 + 1), (g i : ℤ) * gTheoremMatrix d i j.succ.val := by
  obtain ⟨hZero, hDiag, hPref, hRow0, _⟩ :=
    Grunbaum2003.gTheoremMatrix_upper_triangular_and_nonstacked_g2 d hd
  obtain ⟨g, hg, _, _, _, _, _, hRep⟩ :=
    Grunbaum2003.g_theorem_necessity_nonstacked_pos_g2 d hd P hP hV_gt hNonStacked
      ⟨hZero, hDiag, hPref, hRow0⟩
  exact ⟨g, hg, hRep⟩
