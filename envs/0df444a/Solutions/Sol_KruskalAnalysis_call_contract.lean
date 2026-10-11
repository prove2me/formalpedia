-- Prove2me | solution 1 for KruskalAnalysis.call_contract
-- status  : ACCEPTED   (prove)
-- author  : @lunjia
-- created : 2026-10-11T00:07:03.024843+00:00
-- url     : https://prove2.me/submissions/c5eca6d2-b324-4743-bb2d-976356f9d11e

import Definitions.Def_Algo_kruskal_Analysis
import Theorems.Thm_KruskalAnalysis_call_complete


section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true



set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
Clock monotonicity certificates for reusable union-find and sorting components.
Imported algorithms retain their own certificates; client proofs only compose them.
-/

namespace DataStructureClocks

open Algo2LeanCore Algo2LeanGenerated



/-- The binary heap's arithmetic, mutation, and explicit ticks never lower a clock. -/
theorem heap_step {before after : Algo.indexed_heap.Algo2LeanGenerated.Configuration}
    (transition : Algo.indexed_heap.Algo2LeanGenerated.Step before after) :
    before.heap.ClocksMonotone after.heap := by
  cases transition <;> intro clock
  all_goals try simp only [resume_heap]
  all_goals simp [Config.heap, Heap.tick,
      Algo.indexed_heap.Algo2LeanGenerated.set_MinHeap_vertices,
      Algo.indexed_heap.Algo2LeanGenerated.set_MinHeap_positions,
      Algo.indexed_heap.Algo2LeanGenerated.set_MinHeap_keys,
      Algo.indexed_heap.Algo2LeanGenerated.set_MinHeap_size] <;> split <;> omega

/-- The union-find implementation preserves clock monotonicity through recursion. -/
theorem union_find_step {before after : Algo.union_find.Algo2LeanGenerated.Configuration}
    (transition : Algo.union_find.Algo2LeanGenerated.Step before after) :
    before.heap.ClocksMonotone after.heap := by
  cases transition <;> intro clock
  all_goals try simp only [resume_heap]
  all_goals simp [Config.heap, Heap.tick,
      Algo.union_find.Algo2LeanGenerated.set_UnionFind_parent,
      Algo.union_find.Algo2LeanGenerated.set_UnionFind_rank,
      Algo.union_find.Algo2LeanGenerated.set_UnionFind_size] <;> split <;> omega

/-- Sorting reuses the binary heap certificate at imported transitions. -/
theorem sort_step {before after : Algo.sort_indices.Algo2LeanGenerated.Configuration}
    (transition : Algo.sort_indices.Algo2LeanGenerated.Step before after) :
    before.heap.ClocksMonotone after.heap := by
  cases transition <;> try solve
    | intro clock
      try simp only [resume_heap, ModuleCall.heap]
      simp [Config.heap, Heap.tick] <;> split <;> omega
  case import_0 heap frame inner resume caller after delegated =>
    simpa only [ModuleCall.heap] using! heap_step delegated

end DataStructureClocks

end

section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true



set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
Clock counters are monotone through every transition, including delegated calls.
These certificates make cost increments usable with arbitrary initial clocks.
They depend only on the compiled programs, not on graph or data-structure preconditions.
-/

namespace KruskalClocks

open Algo2LeanCore Algo2LeanGenerated DataStructureClocks

/-- Kruskal preserves every clock across its own and imported transitions. -/
theorem kruskal_step {before after : Algo.kruskal.Algo2LeanGenerated.Configuration}
    (transition : Algo.kruskal.Algo2LeanGenerated.Step before after) :
    before.heap.ClocksMonotone after.heap := by
  cases transition <;> try solve
    | intro clock
      try simp only [resume_heap, ModuleCall.heap]
      simp [Config.heap, Heap.tick] <;> split <;> omega
  case import_0 heap frame inner resume caller after delegated =>
    simpa only [ModuleCall.heap] using! union_find_step delegated
  case import_2 heap frame inner resume caller after delegated =>
    simpa only [ModuleCall.heap] using! sort_step delegated

/-- Every completed call has nonnegative increments, whatever counters its
    caller accumulated before invoking Kruskal. -/
theorem call_monotone {before after : Heap} {input result}
    (execution : Algo.kruskal.kruskal.Call before input after result) :
    before.ClocksMonotone after := by
  have preserved := execution.2.root.invariant (fun state => before.ClocksMonotone state.heap)
    (Heap.ClocksMonotone.refl before)
    (fun _ _ transition accumulated => accumulated.trans (kruskal_step transition))
  exact preserved

end KruskalClocks

end

section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true



set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
Kruskal's algorithm on finite undirected weighted graphs. The public interface
uses integer sequences for source vertices, target vertices, edge weights, and
returned selection flags. Correctness and running time reuse the independent
sorting, union-find, and graph analyses.
-/

namespace KruskalAnalysis

open Algo2LeanGenerated Algo.kruskal Algo2Lean.Kruskal
open KruskalInput















/-- Weighted runtime adds across exact clock increments. -/
theorem runtime_increments {before after : Heap} {costs : Clocks}
    (effect : before.Increments after costs) :
    runtime after.clocks = runtime before.clocks + runtime costs := by
  simp only [runtime, SortIndicesAnalysis.runtime, Clocks.weighted, List.map_cons,
    List.map_nil, List.sum_cons, List.sum_nil, work, UnionFindAnalysis.work]
  rw [effect "sort_steps", effect "heap_comparisons", effect "heap_swaps",
    effect "uf_init", effect "uf_find", effect "uf_compress", effect "uf_union", effect "kruskal"]
  omega



/-- The reusable entry-point contract includes fresh output storage, preservation
    of every existing caller location, and the actual increments of all clocks.
    It applies unchanged when called from another algorithm with nonzero clocks. -/
theorem call_contract (heap : Heap) (size count : Int) (sources targets weights : SeqRef)
    (allocated : kruskal.ValidInput heap (size, sources, targets, weights, count))
    (input : WellFormed size count (heap.read sources) (heap.read targets)) :
    ∃ final chosen selected,
      kruskal.Call heap (size, sources, targets, weights, count) final chosen ∧
      MinimumSpanningForest (edges (heap.read sources) (heap.read targets) (heap.read weights) count) selected ∧
      Flags (final.read chosen) selected ∧
      heap.Footprint final [] [] [] ∧ heap.nextRef ≤ chosen ∧ chosen < final.nextRef ∧
      heap.Increments final (Heap.cost heap final) ∧
      runtime (Heap.cost heap final) ≤ runtimeBound size.toNat count.toNat := by
  obtain ⟨final, chosen, selected, execution, minimum, flags, bound, frame, fresh, allocated⟩ :=
    call_complete heap size count sources targets weights allocated input
  have increments := (KruskalClocks.call_monotone execution).increments
  refine ⟨final, chosen, selected, execution, minimum, flags, frame, fresh, allocated, increments, ?_⟩
  rw [runtime_increments increments] at bound
  omega

















-- Main result: Correctness


-- Main result: Running time




end KruskalAnalysis

end

set_option autoImplicit false
theorem solution :
    ∀ (heap : Algo2LeanGenerated.Heap) (size count : Int)
      (sources targets weights : Algo2LeanGenerated.SeqRef),
      Algo.kruskal.kruskal.ValidInput heap
          (Prod.mk.{0, 0} size
            (Prod.mk.{0, 0} sources (Prod.mk.{0, 0} targets (Prod.mk.{0, 0} weights count)))) →
        KruskalInput.WellFormed size count (heap.read sources) (heap.read targets) →
          Exists.{1} fun final =>
            Exists.{1} fun chosen =>
              Exists.{1} fun selected =>
                Algo.kruskal.kruskal.Call heap
                    (Prod.mk.{0, 0} size
                      (Prod.mk.{0, 0} sources (Prod.mk.{0, 0} targets (Prod.mk.{0, 0} weights count))))
                    final chosen ∧
                  Algo2Lean.Kruskal.MinimumSpanningForest
                      (KruskalInput.edges (heap.read sources) (heap.read targets) (heap.read weights)
                        count)
                      selected ∧
                    KruskalAnalysis.Flags (final.read chosen) selected ∧
                      heap.Footprint final List.nil.{0} List.nil.{0} List.nil.{0} ∧
                        LE.le.{0} heap.nextRef chosen ∧
                          LT.lt.{0} chosen final.nextRef ∧
                            heap.Increments final (heap.cost final) ∧
                              LE.le.{0} (KruskalAnalysis.runtime (heap.cost final))
                                (KruskalAnalysis.runtimeBound size.toNat count.toNat) :=
  KruskalAnalysis.call_contract
