-- Prove2me | solution 2 for OAI.SingleFold.DuplicationBound.height_dup_gt_five
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T18:19:01.463986+00:00
-- url     : https://prove2.me/submissions/962e8ccf-cf6b-4e1f-aeec-2ec5e1afa022

-- Generated from openai/math@1581d4c lean/OAI/NumberTheory/SingleFold/Duplication.lean:L190-L202
-- (upload_full_project.md Phase 4): solution for node OAI.SingleFold.DuplicationBound.height_dup_gt_five. The node keeps its source
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
import Theorems.Thm_OAI_SingleFold_DuplicationBound_height_dup_strict
import Theorems.Thm_OAI_SingleFold_DuplicationBound_small_points

-- ---- from OAI.NumberTheory.SingleFold.Duplication ----
namespace OAI

namespace SingleFold.DuplicationBound

lemma height_dup_gt_five {x y : ℚ} (he : y^2=x^3-25*x) (hy : y ≠ 0) :
    5 < height (dupX x) := by
  by_cases hH : 5 ≤ height x
  · exact lt_of_le_of_lt hH (height_dup_strict he hy)
  · rcases small_points he (by omega) with h|h|h|h|h|h|h
    all_goals subst x
    · norm_num at he; exact False.elim (hy he)
    · norm_num at he; exact False.elim (hy he)
    · norm_num at he; exact False.elim (hy he)
    · decide +kernel
    · norm_num [height] at hH
    · norm_num [height] at hH
    · norm_num [height] at hH

end SingleFold.DuplicationBound

end OAI

-- ---- platform node ----
open OAI OAI.SingleFold OAI.SingleFold.DuplicationBound


theorem solution : type_of% @_root_.OAI.SingleFold.DuplicationBound.height_dup_gt_five := @_root_.OAI.SingleFold.DuplicationBound.height_dup_gt_five
