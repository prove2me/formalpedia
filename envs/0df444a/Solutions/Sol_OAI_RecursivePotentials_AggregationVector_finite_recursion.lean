-- Prove2me | solution 1 for OAI.RecursivePotentials.AggregationVector.finite_recursion
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T09:16:15.469064+00:00
-- url     : https://prove2.me/submissions/b650f10d-d2d9-42c7-8717-00c0a07d5034

-- Generated from openai/math@1581d4c lean/OAI/Analysis/RecursivePotentials/VariableStability.lean:L340-L386
-- (upload_full_project.md Phase 4): solution for node OAI.RecursivePotentials.AggregationVector.finite_recursion. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_RecursivePotentials
import Definitions.Def_OAI_Analysis_RecursivePotentials_Model
import Definitions.Def_OAI_Analysis_RecursivePotentials_TreeGeometry
import Definitions.Def_OAI_Analysis_RecursivePotentials_ZeroRootGeometry
import Definitions.Def_OAI_Analysis_RecursivePotentials_EquivalentNorms
import Definitions.Def_OAI_Analysis_RecursivePotentials_JoinedGeometry
import Definitions.Def_OAI_Analysis_RecursivePotentials_VariableEstimates
import Definitions.Def_OAI_Analysis_RecursivePotentials_VariableCompletion
import Definitions.Def_OAI_Analysis_RecursivePotentials_VariableLp
import Definitions.Def_OAI_Analysis_RecursivePotentials_VariableStability

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

end

variable {ι : Type uIndex} [indexDecidable : DecidableEq ι] (T : FiniteRootedTree ι)

lemma ancestors_subset_of_initial {H : Finset ι} (hH : T.Initial H) (s : ι) (hs : s ∈ H) :
    T.ancestors s ⊆ H := by
  rw [ancestors]
  split_ifs with heq
  · simpa
  · exact Finset.insert_subset hs (ancestors_subset_of_initial hH (T.parent s) (hH.2 s hs))
termination_by T.depth s
decreasing_by exact T.parent_depth s heq

lemma ancestorClosure_subset_of_initial {S H : Finset ι} (hH : T.Initial H) (hS : S ⊆ H) :
    T.ancestorClosure S ⊆ H := by
  apply Finset.insert_subset hH.1
  intro s hs
  obtain ⟨c, hc, hs⟩ := Finset.mem_biUnion.mp hs
  exact T.ancestors_subset_of_initial hH c (hS hc) hs

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

-- ---- from OAI.Analysis.RecursivePotentials.VariableCompletion ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

noncomputable section

universe uIndex uSpace uOther uDomain uTarget uFiber

open scoped BigOperators

namespace RecursivePotentials

open Filter Topology

open Filter Topology

open scoped ENNReal

open UniformSpace

open Filter

open scoped Topology

namespace VariableTree

open FiniteRootedTree

variable {ι : Type uIndex} [indexDecidable : DecidableEq ι] (T : FiniteRootedTree ι)
    (e : ChildExponent)

lemma P_eq_zero_off_head (v : ι →₀ ℝ) {H : Finset ι} (hH : T.Initial H)
    (hv : v.support ⊆ H) {s : ι} (hs : s ∉ H) : P T e v s = 0 := by
  apply extend_not_mem
  exact fun hh => hs (T.ancestorClosure_subset_of_initial hH hv hh)

lemma Q_eq_zero_off_head (v : ι →₀ ℝ) {H : Finset ι} (hH : T.Initial H)
    (hv : v.support ⊆ H) {s : ι} (hs : s ∉ H) : Q T e v s = 0 := by
  apply extend_not_mem
  exact fun hh => hs (T.ancestorClosure_subset_of_initial hH hv hh)

end VariableTree

namespace AggregationVector

variable {ι : Type uIndex} [indexDecidable : DecidableEq ι] (T : FiniteRootedTree ι)
    (e : ChildExponent)

end AggregationVector

namespace AggregationSpace

open UniformSpace

variable {ι : Type uIndex} [indexDecidable : DecidableEq ι] (T : FiniteRootedTree ι)
    (e : ChildExponent)

end AggregationSpace

namespace AggregationVector

variable {ι : Type uIndex} [indexDecidable : DecidableEq ι] (T : FiniteRootedTree ι)
    (e : ChildExponent)

end AggregationVector

namespace AggregationSpace

open UniformSpace

variable {ι : Type uIndex} [indexDecidable : DecidableEq ι] (T : FiniteRootedTree ι)
    (e : ChildExponent)

end AggregationSpace

namespace VariableExponent

end VariableExponent

namespace VariableTree

open VariableExponent

variable {ι : Type uIndex} [indexDecidable : DecidableEq ι] (T : FiniteRootedTree ι)
    (e : ChildExponent)

end VariableTree

namespace AggregationSpace

open UniformSpace VariableExponent

variable {ι : Type uIndex} [indexDecidable : DecidableEq ι] (T : FiniteRootedTree ι)
    (e : ChildExponent)

end AggregationSpace

end RecursivePotentials

end

end OAI

-- ---- from OAI.Analysis.RecursivePotentials.VariableStability ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe uIndex uSpace uOther uDomain uTarget uFiber

open scoped BigOperators

namespace RecursivePotentials

open Filter Topology

open Filter Topology

open scoped ENNReal

open UniformSpace

open Filter

open scoped Topology

open Filter Topology TopologicalSpace

open scoped ENNReal

namespace VariableExponent

noncomputable section

section Outer

variable {ι : Type uIndex} [indexDecidable : DecidableEq ι] (E : ι → Type uFiber)
  [∀ i, NormedAddCommGroup (E i)] [fiberNormedSpace : ∀ i, NormedSpace ℝ (E i)]

end Outer

end

end VariableExponent

namespace AggregationVector

noncomputable section

open FiniteRootedTree

variable {ι : Type uIndex} [indexDecidable : DecidableEq ι] (T : FiniteRootedTree ι)
    (e : ChildExponent)

lemma childLp_norm_eq (s : ι) (f : ι →₀ ℝ) (H : Finset ι) (hf : f.support ⊆ H) :
    ‖childLp T e s f‖ = e.agg (H.filter fun c => c ≠ T.root ∧ T.parent c = s) f := by
  apply (Real.rpow_left_inj (norm_nonneg _) (e.agg_nonneg _ _) e.ne_zero).mp
  change ‖toLpLinear T e (show AggregationVector T e from f.filter fun c => c ≠ T.root ∧ T.parent c = s)‖ ^ e.val = _
  rw [toLpLinear_norm_rpow,e.agg_rpow]
  have hs : (f.filter fun c => c ≠ T.root ∧ T.parent c = s).support ⊆
      H.filter (fun c => c ≠ T.root ∧ T.parent c = s) := by
    intro c hc
    rw [Finsupp.support_filter] at hc
    exact Finset.mem_filter.mpr ⟨hf (Finset.mem_filter.mp hc).1,(Finset.mem_filter.mp hc).2⟩
  calc
    _ = ∑ c ∈ (f.filter fun c => c ≠ T.root ∧ T.parent c = s).support, |f c| ^ e.val := by
      apply Finset.sum_congr rfl
      intro c hc
      rw [Finsupp.support_filter] at hc
      simp [(Finset.mem_filter.mp hc).2]
    _ = _ := Finset.sum_subset hs (fun c hc hn => by
      have hfc : f c = 0 := by
        apply Finsupp.notMem_support_iff.mp
        intro hh
        exact hn (by rw [Finsupp.support_filter]; exact Finset.mem_filter.mpr ⟨hh,(Finset.mem_filter.mp hc).2⟩)
      rw [hfc,abs_zero,Real.zero_rpow e.ne_zero])

lemma finite_recursion (s : ι) (v : AggregationVector T e) :
    (VariableTree.P T e v s,VariableTree.Q T e v s) =
      leastPair (v s) ‖childP T e s v‖ ‖childQ T e s v‖ := by
  let H := T.head v
  have hH : T.Initial H := T.head_initial v
  have hP : (VariableTree.P T e v).support ⊆ H := by
    intro c hc; by_contra hn
    exact Finsupp.mem_support_iff.mp hc (VariableTree.P_eq_zero_off_head T e v hH (T.support_subset_head v) hn)
  have hQ : (VariableTree.Q T e v).support ⊆ H := by
    intro c hc; by_contra hn
    exact Finsupp.mem_support_iff.mp hc (VariableTree.Q_eq_zero_off_head T e v hH (T.support_subset_head v) hn)
  rw [childP,childQ,childLp_norm_eq T e s _ H hP,childLp_norm_eq T e s _ H hQ]
  by_cases hs : s ∈ H
  · have h := VariableTree.potentials_on_head T e v H hH (T.support_subset_head v) ⟨s,hs⟩
    have hAggP : e.agg ((T.restrict H hH).children ⟨s,hs⟩)
        (fun c => ((T.restrict H hH).pfields e (fun c => v c.1) c).1) =
        e.agg (H.filter fun c => c ≠ T.root ∧ T.parent c = s) (VariableTree.P T e v) := by
      unfold ChildExponent.agg
      congr 1
      rw [← T.sum_restrict_children H hH ⟨s,hs⟩]
      apply Finset.sum_congr rfl
      intro c hc
      rw [(VariableTree.potentials_on_head T e v H hH (T.support_subset_head v) c).1]
    have hAggQ : e.agg ((T.restrict H hH).children ⟨s,hs⟩)
        (fun c => ((T.restrict H hH).pfields e (fun c => v c.1) c).2) =
        e.agg (H.filter fun c => c ≠ T.root ∧ T.parent c = s) (VariableTree.Q T e v) := by
      unfold ChildExponent.agg
      congr 1
      rw [← T.sum_restrict_children H hH ⟨s,hs⟩]
      apply Finset.sum_congr rfl
      intro c hc
      rw [(VariableTree.potentials_on_head T e v H hH (T.support_subset_head v) c).2]
    calc
      _ = (T.restrict H hH).pfields e (fun c => v c.1) ⟨s,hs⟩ := Prod.ext h.1 h.2
      _ = _ := by rw [(T.restrict H hH).pfields_eq,hAggP,hAggQ]
  · have hc : H.filter (fun c => c ≠ T.root ∧ T.parent c = s) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro c hc
      obtain ⟨hcH,hc⟩ := Finset.mem_filter.mp hc
      have hh := hH.2 c hcH
      rw [hc.2] at hh
      exact hs hh
    rw [hc,e.agg_empty,e.agg_empty,
      VariableTree.P_eq_zero_off_head T e v hH (T.support_subset_head v) hs,
      VariableTree.Q_eq_zero_off_head T e v hH (T.support_subset_head v) hs,
      T.zero_off_head v hs]
    norm_num [leastPair]

end

end AggregationVector

namespace AggregationSpace

noncomputable section

open UniformSpace

variable {ι : Type uIndex} [indexDecidable : DecidableEq ι] (T : FiniteRootedTree ι)
    (e : ChildExponent)

end

end AggregationSpace

namespace Variable

noncomputable section

open UniformSpace VariableExponent Filter Topology TopologicalSpace

end

end Variable

namespace ScalarLp

noncomputable section

open Filter Topology

variable {ι : Type uIndex} [indexDecidable : DecidableEq ι]

end

end ScalarLp

namespace Variable

noncomputable section

open UniformSpace VariableExponent Filter Topology TopologicalSpace

end

end Variable

end RecursivePotentials

end OAI

-- ---- platform node ----
open OAI OAI.RecursivePotentials OAI.RecursivePotentials.AggregationVector
open scoped BigOperators
open Filter Topology
open Filter Topology
open scoped ENNReal
open UniformSpace
open Filter
open scoped Topology
open Filter Topology TopologicalSpace
open scoped ENNReal
open FiniteRootedTree


theorem solution.{uIndex} : type_of% @_root_.OAI.RecursivePotentials.AggregationVector.finite_recursion.{uIndex} := @_root_.OAI.RecursivePotentials.AggregationVector.finite_recursion.{uIndex}
