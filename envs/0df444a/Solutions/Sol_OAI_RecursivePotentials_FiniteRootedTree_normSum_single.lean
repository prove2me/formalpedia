-- Prove2me | solution 1 for OAI.RecursivePotentials.FiniteRootedTree.normSum_single
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T08:50:38.867985+00:00
-- url     : https://prove2.me/submissions/0b8388c9-3763-4eec-80f7-57fed5720a57

-- Generated from openai/math@1581d4c lean/OAI/Analysis/RecursivePotentials/ZeroRootGeometry.lean:L508-L520
-- (upload_full_project.md Phase 4): solution for node OAI.RecursivePotentials.FiniteRootedTree.normSum_single. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_RecursivePotentials
import Definitions.Def_OAI_Analysis_RecursivePotentials_Model
import Definitions.Def_OAI_Analysis_RecursivePotentials_TreeGeometry
import Definitions.Def_OAI_Analysis_RecursivePotentials_ZeroRootGeometry
import Theorems.Thm_OAI_RecursivePotentials_FiniteRootedTree_normSum_siblings_le
import Theorems.Thm_OAI_RecursivePotentials_FiniteRootedTree_twice_coordinate_le_normSum

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

lemma normSum_single (c : ι) (hc : c ≠ T.root) :
    T.normSum (Finsupp.single c 1) = 2 := by
  have hl := T.twice_coordinate_le_normSum (Finsupp.single c 1) (by simp [hc]) c
  simp only [Finsupp.single_eq_same, abs_one, mul_one] at hl
  have hu := T.normSum_siblings_le (T.parent c) (Finsupp.single c 1) (by
    intro s hs
    have he : s = c := by simpa using hs
    subst s
    exact ⟨hc, rfl⟩)
  have hsum : ∑ s ∈ (Finsupp.single c (1 : ℝ)).support, (Finsupp.single c (1 : ℝ) s) ^ 2 = 1 := by
    simp
  rw [hsum, Real.sqrt_one, mul_one] at hu
  exact le_antisymm hu hl

end FiniteRootedTree

end RecursivePotentials

end

end OAI

-- ---- platform node ----
open OAI OAI.RecursivePotentials OAI.RecursivePotentials.FiniteRootedTree
open scoped BigOperators


theorem solution.{uIndex} : type_of% @_root_.OAI.RecursivePotentials.FiniteRootedTree.normSum_single.{uIndex} := @_root_.OAI.RecursivePotentials.FiniteRootedTree.normSum_single.{uIndex}
