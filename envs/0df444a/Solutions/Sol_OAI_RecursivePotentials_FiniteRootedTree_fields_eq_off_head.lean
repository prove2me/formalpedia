-- Prove2me | solution 1 for OAI.RecursivePotentials.FiniteRootedTree.fields_eq_off_head
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T08:26:13.459892+00:00
-- url     : https://prove2.me/submissions/f265bc4f-7661-44b3-a3e1-af7b9c671cdf

-- Generated from openai/math@1581d4c lean/OAI/Analysis/RecursivePotentials/TreeGeometry.lean:L362-L376
-- (upload_full_project.md Phase 4): solution for node OAI.RecursivePotentials.FiniteRootedTree.fields_eq_off_head. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_RecursivePotentials
import Definitions.Def_OAI_Analysis_RecursivePotentials_Model
import Definitions.Def_OAI_Analysis_RecursivePotentials_TreeGeometry

-- ---- from OAI.Analysis.RecursivePotentials.TreeGeometry ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

noncomputable section

universe uIndex uSpace uOther uDomain uTarget uFiber

open scoped BigOperators

namespace RecursivePotentials

namespace FiniteRootedTree

section

variable {ι : Type uIndex} [indexFinite : Fintype ι] [indexDecidable : DecidableEq ι]
    (T : FiniteRootedTree ι)

lemma Initial.child_not_mem {H : Finset ι} (hH : T.Initial H) {s c : ι}
    (hs : s ∉ H) (hc : c ∈ T.children s) : c ∉ H := by
  intro h
  have := hH.2 c h
  have hh := (Finset.mem_filter.mp hc).2.2
  exact hs (hh ▸ this)

theorem fields_eq_off_head {H : Finset ι} (hH : T.Initial H) (v w : ι → ℝ)
    (hvw : ∀ s ∉ H, v s = w s) (s : ι) (hs : s ∉ H) :
    T.fields v s = T.fields w s := by
  rw [T.fields_eq v s, T.fields_eq w s, hvw s hs]
  apply congrArg₂ (leastPair (w s))
  · apply congrArg Real.sqrt
    apply Finset.sum_congr rfl
    intro c hc
    rw [fields_eq_off_head hH v w hvw c (hH.child_not_mem T hs hc)]
  · apply congrArg Real.sqrt
    apply Finset.sum_congr rfl
    intro c hc
    rw [fields_eq_off_head hH v w hvw c (hH.child_not_mem T hs hc)]
termination_by T.maxDepth - T.depth s
decreasing_by all_goals exact T.child_measure hc

end

variable {ι : Type uIndex} [indexDecidable : DecidableEq ι] (T : FiniteRootedTree ι)

end FiniteRootedTree

namespace TreeVector

variable {ι : Type uIndex} [indexDecidable : DecidableEq ι] (T : FiniteRootedTree ι)

end TreeVector

namespace TreeSpace

open UniformSpace

variable {ι : Type uIndex} [indexDecidable : DecidableEq ι] (T : FiniteRootedTree ι)

end TreeSpace

namespace FiniteRootedTree

variable {ι : Type uIndex} [indexDecidable : DecidableEq ι] (T : FiniteRootedTree ι)

end FiniteRootedTree

namespace TreeSpace

open UniformSpace

variable {ι : Type uIndex} [indexDecidable : DecidableEq ι] (T : FiniteRootedTree ι)

end TreeSpace

namespace TreeVector

variable {ι : Type uIndex} [indexDecidable : DecidableEq ι] (T : FiniteRootedTree ι)

end TreeVector

namespace TreeSpace

open UniformSpace

variable {ι : Type uIndex} [indexDecidable : DecidableEq ι] (T : FiniteRootedTree ι)

end TreeSpace

namespace CofiniteSubspace

variable {E : Type uSpace} [NormedAddCommGroup E] [NormedSpace ℝ E]

end CofiniteSubspace

section Moduli

variable {E : Type uSpace} [NormedAddCommGroup E] [NormedSpace ℝ E]

end Moduli

namespace TreeSpace

open UniformSpace

variable {ι : Type uIndex} [indexDecidable : DecidableEq ι] (T : FiniteRootedTree ι)

end TreeSpace

end RecursivePotentials

end

end OAI

-- ---- platform node ----
open OAI OAI.RecursivePotentials OAI.RecursivePotentials.FiniteRootedTree
open scoped BigOperators


theorem solution.{uIndex} : type_of% @_root_.OAI.RecursivePotentials.FiniteRootedTree.fields_eq_off_head.{uIndex} := @_root_.OAI.RecursivePotentials.FiniteRootedTree.fields_eq_off_head.{uIndex}
