-- Prove2me | solution 1 for OAI.SingleFold.DuplicationBound.height_dup_strict
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T18:17:21.794001+00:00
-- url     : https://prove2.me/submissions/cf08f337-b5af-401d-8a8a-40319041b196

-- Generated from openai/math@1581d4c lean/OAI/NumberTheory/SingleFold/Duplication.lean:L166-L188
-- (upload_full_project.md Phase 4): solution for node OAI.SingleFold.DuplicationBound.height_dup_strict. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_SingleFold
import Definitions.Def_OAI_NumberTheory_SingleFold_PolynomialCompiler
import Definitions.Def_OAI_NumberTheory_SingleFold_RationalCodes
import Definitions.Def_OAI_NumberTheory_SingleFold_EllipticCoordinates
import Definitions.Def_OAI_NumberTheory_SingleFold_FunctionalCompiler
import Definitions.Def_OAI_NumberTheory_SingleFold_DescentMap
import Definitions.Def_OAI_NumberTheory_SingleFold_SquareSupport
import Definitions.Def_OAI_NumberTheory_SingleFold_LocalDescent
import Definitions.Def_OAI_NumberTheory_SingleFold_EllipticHeight
import Definitions.Def_OAI_NumberTheory_SingleFold_QuadraticHeight
import Definitions.Def_OAI_NumberTheory_SingleFold_FiniteGeneration
import Definitions.Def_OAI_NumberTheory_SingleFold_Rank
import Definitions.Def_OAI_NumberTheory_SingleFold_Duplication
import Theorems.Thm_OAI_SingleFold_DuplicationBound_height_dup_lower
import Theorems.Thm_OAI_SingleFold_DuplicationBound_small_points

-- ---- from OAI.NumberTheory.SingleFold.Duplication ----
namespace OAI

namespace SingleFold.DuplicationBound

lemma height_dup_strict {x y : ℚ} (he : y^2=x^3-25*x) (hy : y ≠ 0) :
    height x < height (dupX x) := by
  have hx : x ≠ 0 := by intro h; rw [h] at he; simp at he; exact hy he
  have hs : x^2-25 ≠ 0 := by
    intro h
    have hh : y^2=0 := by linear_combination he+x*h
    exact hy (sq_eq_zero_iff.mp hh)
  by_cases hH : height x < 185
  · rcases small_points he hH with h|h|h|h|h|h|h
    · exact False.elim (hx h)
    · subst x; norm_num at hs
    · subst x; norm_num at hs
    · subst x; decide +kernel
    · subst x; decide +kernel
    · subst x; decide +kernel
    · subst x; decide +kernel
  · have hH' : 185 ≤ height x := by omega
    have hc : 6250000 < height x ^ 3 := lt_of_lt_of_le (by norm_num) (Nat.pow_le_pow_left hH' 3)
    have hhp : 0 < height x := by omega
    have hmul := Nat.mul_lt_mul_of_pos_right hc hhp
    have hmul' : 6250000*height x < height x^4 := by simpa [pow_succ] using hmul
    have hl := height_dup_lower x hx hs
    nlinarith only [hmul',hl]

end SingleFold.DuplicationBound

end OAI

-- ---- platform node ----
open OAI OAI.SingleFold OAI.SingleFold.DuplicationBound


theorem solution : type_of% @_root_.OAI.SingleFold.DuplicationBound.height_dup_strict := @_root_.OAI.SingleFold.DuplicationBound.height_dup_strict
