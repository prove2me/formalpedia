-- Prove2me | solution 1 for OAI.RecursivePotentials.TreeSpace.siblings_weaklyNull
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T08:58:31.787784+00:00
-- url     : https://prove2.me/submissions/55436f67-8c0b-4b8d-8fb4-07210716f82f

-- Generated from openai/math@1581d4c lean/OAI/Analysis/RecursivePotentials/EquivalentNorms.lean:L390-L415
-- (upload_full_project.md Phase 4): solution for node OAI.RecursivePotentials.TreeSpace.siblings_weaklyNull. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_RecursivePotentials
import Definitions.Def_OAI_Analysis_RecursivePotentials_Model
import Definitions.Def_OAI_Analysis_RecursivePotentials_TreeGeometry
import Definitions.Def_OAI_Analysis_RecursivePotentials_ZeroRootGeometry
import Definitions.Def_OAI_Analysis_RecursivePotentials_EquivalentNorms
import Theorems.Thm_OAI_RecursivePotentials_FiniteRootedTree_normSum_siblings_le
import Theorems.Thm_OAI_RecursivePotentials_weaklyNull_of_finsupp_bound

-- ---- from OAI.Analysis.RecursivePotentials.EquivalentNorms ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe uIndex uSpace uOther uDomain uTarget uFiber

open scoped BigOperators

namespace RecursivePotentials

open Filter Topology

namespace EquivalentNorm

variable {E : Type uSpace} [NormedAddCommGroup E] [NormedSpace ℝ E] (A : EquivalentNorm E)

end EquivalentNorm

namespace FiniteRootedTree

variable {ι : Type uIndex} [indexDecidable : DecidableEq ι] (T : FiniteRootedTree ι)

lemma normSum_emb_siblings (s : ι) (f : ℕ ↪ ι)
    (hf : ∀ k, f k ≠ T.root ∧ T.parent (f k) = s) (a : ℕ →₀ ℝ) :
    T.normSum (a.embDomain f) ≤ 2 * Real.sqrt (∑ k ∈ a.support, a k ^ 2) := by
  have h := T.normSum_siblings_le s (a.embDomain f) (by
    intro c hc
    rw [Finsupp.support_embDomain] at hc
    obtain ⟨k, hk, rfl⟩ := Finset.mem_map.mp hc
    exact hf k)
  simpa only [Finsupp.support_embDomain, Finset.sum_map, Finsupp.embDomain_apply_self] using h

end FiniteRootedTree

namespace TreeSpace

noncomputable section

variable {ι : Type uIndex} [indexDecidable : DecidableEq ι] (T : FiniteRootedTree ι)

open UniformSpace

lemma siblings_weaklyNull (s : ι) (f : ℕ ↪ ι)
    (hf : ∀ k, f k ≠ T.root ∧ T.parent (f k) = s) :
    WeaklyNull (fun k => basisVector T (f k)) := by
  let L : (ℕ →₀ ℝ) →ₗ[ℝ] TreeVector T :=
    { toFun := Finsupp.embDomain f
      map_add' := Finsupp.embDomain_add f
      map_smul' := by
        intro r a
        change Finsupp.embDomain f (r • a) = r • Finsupp.embDomain f a
        ext c
        by_cases hc : c ∈ Set.range f
        · obtain ⟨k, rfl⟩ := hc
          simp only [Finsupp.embDomain_apply_self, Finsupp.smul_apply]
        · simp only [Finsupp.embDomain_of_notMem_range f _ c hc, Finsupp.smul_apply, smul_zero] }
  let D : (ℕ →₀ ℝ) →ₗ[ℝ] TreeSpace T :=
    (Completion.toComplL : TreeVector T →L[ℝ] TreeSpace T).toLinearMap.comp L
  have he : ∀ k, D (Finsupp.single k 1) = basisVector T (f k) := by
    intro k
    change (↑(show TreeVector T from Finsupp.embDomain f (Finsupp.single k 1)) : TreeSpace T) = _
    rw [Finsupp.embDomain_single]; rfl
  simp_rw [← he]
  refine weaklyNull_of_finsupp_bound D (by norm_num : (0 : ℝ) ≤ 2) ?_
  intro a
  change ‖(↑(show TreeVector T from a.embDomain f) : TreeSpace T)‖ ≤ _
  rw [Completion.norm_coe, TreeVector.norm_def]
  exact T.normSum_emb_siblings s f hf a

end

end TreeSpace

namespace TreeSpace

noncomputable section

variable {ι : Type uIndex} [indexDecidable : DecidableEq ι] (T : FiniteRootedTree ι)

open UniformSpace

end

end TreeSpace

namespace ZeroTreeSpace

noncomputable section

variable {ι : Type uIndex} [indexDecidable : DecidableEq ι] (T : FiniteRootedTree ι)

open UniformSpace

end

end ZeroTreeSpace

namespace EquivalentNorm

variable {E : Type uSpace} [NormedAddCommGroup E] [NormedSpace ℝ E] (A : EquivalentNorm E)

end EquivalentNorm

end RecursivePotentials

end OAI

-- ---- platform node ----
open OAI OAI.RecursivePotentials OAI.RecursivePotentials.TreeSpace
open scoped BigOperators
open Filter Topology
open UniformSpace


theorem solution.{uIndex} : type_of% @_root_.OAI.RecursivePotentials.TreeSpace.siblings_weaklyNull.{uIndex} := @_root_.OAI.RecursivePotentials.TreeSpace.siblings_weaklyNull.{uIndex}
