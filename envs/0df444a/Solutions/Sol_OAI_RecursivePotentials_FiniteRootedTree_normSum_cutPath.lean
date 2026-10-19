-- Prove2me | solution 1 for OAI.RecursivePotentials.FiniteRootedTree.normSum_cutPath
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T08:52:16.018986+00:00
-- url     : https://prove2.me/submissions/ebc13515-eeb6-4de5-b115-754ff09bba6d

-- Generated from openai/math@1581d4c lean/OAI/Analysis/RecursivePotentials/ZeroRootGeometry.lean:L527-L547
-- (upload_full_project.md Phase 4): solution for node OAI.RecursivePotentials.FiniteRootedTree.normSum_cutPath. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_RecursivePotentials
import Definitions.Def_OAI_Analysis_RecursivePotentials_Model
import Definitions.Def_OAI_Analysis_RecursivePotentials_TreeGeometry
import Definitions.Def_OAI_Analysis_RecursivePotentials_ZeroRootGeometry
import Theorems.Thm_OAI_RecursivePotentials_FiniteRootedTree_twice_coordinate_le_normSum

-- ---- from OAI.Analysis.RecursivePotentials.ZeroRootGeometry ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e
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

lemma normSum_cutPath (s : ι) (hs : s ≠ T.root) : T.normSum (T.cutPath s) = 2 := by
  have hv : T.cutPath s s = 1 := by
    simp [cutPath, path_apply, T.mem_ancestors_self, Ne.symm hs]
  have hl := T.twice_coordinate_le_normSum (T.cutPath s) (T.cutPath_root s) s
  rw [hv, abs_one, mul_one] at hl
  let b : ι → ℝ := (Finsupp.single T.root 1 : ι →₀ ℝ)
  have hb : T.GlobalUpper b := by
    intro a S hS
    have he : ∑ c ∈ S, b c ^ 2 = 0 := by
      apply Finset.sum_eq_zero
      intro c hc
      simp only [b, Finsupp.single_apply, ite_eq_right (Ne.symm (hS c hc).1), zero_pow (by omega : 2 ≠ 0)]
    rw [he]
    exact sq_nonneg _
  have hu := T.potentials_minimal (T.cutPath s) (T.path s) b (T.path_nonneg s)
    (fun c => by dsimp [b]; simp only [Finsupp.single_apply]; split_ifs <;> norm_num)
    (fun c => rfl) (T.path_upper s) hb T.root
  have hb0 : b T.root = 1 := by simp [b]
  rw [T.path_root, hb0] at hu
  unfold normSum
  exact le_antisymm (by linarith [hu.1, hu.2]) hl

end FiniteRootedTree

end RecursivePotentials

end

end OAI

-- ---- platform node ----
open OAI OAI.RecursivePotentials OAI.RecursivePotentials.FiniteRootedTree
open scoped BigOperators


theorem solution.{uIndex} : type_of% @_root_.OAI.RecursivePotentials.FiniteRootedTree.normSum_cutPath.{uIndex} := @_root_.OAI.RecursivePotentials.FiniteRootedTree.normSum_cutPath.{uIndex}
