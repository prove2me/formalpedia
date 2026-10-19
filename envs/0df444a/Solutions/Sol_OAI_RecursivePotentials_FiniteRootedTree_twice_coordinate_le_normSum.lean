-- Prove2me | solution 1 for OAI.RecursivePotentials.FiniteRootedTree.twice_coordinate_le_normSum
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T08:49:07.578564+00:00
-- url     : https://prove2.me/submissions/df58cb7d-51cb-4189-bc2c-18df9d6f3b14

-- Generated from openai/math@1581d4c lean/OAI/Analysis/RecursivePotentials/ZeroRootGeometry.lean:L492-L506
-- (upload_full_project.md Phase 4): solution for node OAI.RecursivePotentials.FiniteRootedTree.twice_coordinate_le_normSum. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_RecursivePotentials
import Definitions.Def_OAI_Analysis_RecursivePotentials_Model
import Definitions.Def_OAI_Analysis_RecursivePotentials_TreeGeometry
import Definitions.Def_OAI_Analysis_RecursivePotentials_ZeroRootGeometry

-- ---- from OAI.Analysis.RecursivePotentials.ZeroRootGeometry ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

noncomputable section

universe uIndex uSpace uOther uDomain uTarget uFiber

open scoped BigOperators

namespace RecursivePotentials

namespace ZeroTreeVector

variable {ι : Type uIndex} [indexDecidable : DecidableEq ι] (T : FiniteRootedTree ι)

end ZeroTreeVector

namespace ZeroTreeSpace

open UniformSpace

variable {ι : Type uIndex} [indexDecidable : DecidableEq ι] (T : FiniteRootedTree ι)

end ZeroTreeSpace

namespace ZeroTreeVector

variable {ι : Type uIndex} [indexDecidable : DecidableEq ι] (T : FiniteRootedTree ι)

end ZeroTreeVector

namespace ZeroTreeSpace

open UniformSpace

variable {ι : Type uIndex} [indexDecidable : DecidableEq ι] (T : FiniteRootedTree ι)

end ZeroTreeSpace

namespace FiniteRootedTree

variable {ι : Type uIndex} [indexDecidable : DecidableEq ι] (T : FiniteRootedTree ι)

lemma twice_coordinate_le_normSum (v : ι →₀ ℝ) (hv : v T.root = 0) (s : ι) :
    2 * |v s| ≤ T.normSum v := by
  have hd := T.P_sub_Q v T.root
  rw [hv] at hd
  have hp := (T.P_upper v).le_root T (T.P_nonneg v) s
  have hq := (T.Q_upper v).le_root T (T.Q_nonneg v) s
  have hc := T.P_sub_Q v s
  have hp0 := T.P_nonneg v s
  have hq0 := T.Q_nonneg v s
  unfold normSum
  rcases le_total 0 (v s) with hs | hs
  · rw [abs_of_nonneg hs]
    linarith
  · rw [abs_of_nonpos hs]
    linarith

end FiniteRootedTree

end RecursivePotentials

end

end OAI

-- ---- platform node ----
open OAI OAI.RecursivePotentials OAI.RecursivePotentials.FiniteRootedTree
open scoped BigOperators


theorem solution.{uIndex} : type_of% @_root_.OAI.RecursivePotentials.FiniteRootedTree.twice_coordinate_le_normSum.{uIndex} := @_root_.OAI.RecursivePotentials.FiniteRootedTree.twice_coordinate_le_normSum.{uIndex}
