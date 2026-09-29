-- Prove2me | solution 1 for KServer.chunk_expTotal_le_evader_cost
-- status  : ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-09-10T10:17:59.225078+00:00
-- url     : https://prove2.me/submissions/3acf580e-e0fd-4a2e-b912-04cf5ce6d3ec

import Mathlib
import Definitions.Def_KServer_model
import Definitions.Def_KServer_evader
import Definitions.Def_KServer_evader_bail
import Definitions.Def_KServer_chunk_system_b
import Definitions.Def_KServer_chunk_cond
import Definitions.Def_KServer_chunk_saturate

set_option linter.unusedTactic false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

open KServer


/-!
# The expected total size of a chunk system is bounded by any evader's cost

For every chunk system with online escapes `C` and every evader `E`, the expected total
size of `C` is at most the expected cost of `E` on the request sequence of `C`.
-/



namespace EvaderBound

variable {X : Type*} [MetricSpace X] {s t : X} {cLo cHi total price : ℝ} {mL : ℕ}
variable (C : ChunkSystemB X s t cLo cHi total price mL)

/-- The request history preceding chunk `i`. -/
noncomputable def pre (i : ℕ) (ω : C.Ω) : List (Set X) :=
  ((List.ofFn (C.chunk ω)).take i).flatten

/-- Chunk `i`, indexed by a natural number (empty beyond the last chunk). -/
noncomputable def chunkN (i : ℕ) (ω : C.Ω) : List (Set X) :=
  if h : i < C.m then C.chunk ω ⟨i, h⟩ else []

/-- Size of chunk `i`, indexed by a natural number (zero beyond the last chunk). -/
noncomputable def sizeN (i : ℕ) (ω : C.Ω) : ℝ :=
  if h : i < C.m then C.size ω ⟨i, h⟩ else 0

theorem bailCost_never {Y : Type*} [MetricSpace Y] (E : EvaderAlgorithm Y)
    (h χ : List (Set Y)) (p : ℝ) : E.bailCost (fun _ => false) h χ p = E.costOn h χ := by
  unfold EvaderAlgorithm.bailCost bailTime
  have hnone : List.find? (fun _ => false) (List.range χ.length) = none :=
    List.find?_eq_none.mpr (by simp)
  rw [hnone]

theorem cost_nil (E : EvaderAlgorithm X) : E.cost [] = 0 := by
  simp [EvaderAlgorithm.cost]

theorem pre_zero (ω : C.Ω) : pre C 0 ω = [] := by simp [pre]

theorem pre_m (ω : C.Ω) : pre C C.m ω = C.seq ω := by
  unfold pre ChunkSystemB.seq
  rw [List.take_of_length_le (by simp)]

theorem pre_succ (i : ℕ) (ω : C.Ω) :
    pre C (i + 1) ω = pre C i ω ++ chunkN C i ω := by
  unfold pre chunkN
  have hlen : (List.ofFn (C.chunk ω)).length = C.m := by simp
  by_cases hi : i < C.m
  · have h1 : (List.ofFn (C.chunk ω)).take (i + 1)
        = (List.ofFn (C.chunk ω)).take i ++ [C.chunk ω ⟨i, hi⟩] := by
      rw [List.take_add_one]
      congr 1
      rw [List.getElem?_eq_getElem (by rw [hlen]; exact hi)]
      simp
    rw [h1, List.flatten_append, dif_pos hi]
    simp
  · have h1 : (List.ofFn (C.chunk ω)).take (i + 1) = (List.ofFn (C.chunk ω)).take i := by
      rw [List.take_of_length_le (by omega), List.take_of_length_le (by omega)]
    rw [h1, dif_neg hi]
    simp

/-- One chunk: the expected size is at most the expected cost of the evader on that
chunk. -/
theorem sum_sizeN_le_sum_costOn (E : EvaderAlgorithm X) (i : ℕ) :
    ∑ ω, C.P ω * sizeN C i ω
      ≤ ∑ ω, C.P ω * E.costOn (pre C i ω) (chunkN C i ω) := by
  classical
  by_cases hi : i < C.m
  · refine C.sum_saturated_le i Finset.univ (fun _ _ ω' _ => Finset.mem_univ ω') _ _ ?_
    intro ω₁ _
    have hc := C.hcost ⟨i, hi⟩ ω₁ E (fun _ => false)
    simp only [bailCost_never] at hc
    have hL : ∑ ω' ∈ C.atom i ω₁, C.P ω' * sizeN C i ω'
        = C.size ω₁ ⟨i, hi⟩ * ∑ ω' ∈ C.atom i ω₁, C.P ω' := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun ω' hm' => ?_
      unfold sizeN
      rw [dif_pos hi, C.hsmeas ⟨i, hi⟩ ω' ω₁ (C.mem_atom.mp hm')]
      ring
    have hR : ∑ ω' ∈ C.atom i ω₁, C.P ω' * E.costOn (pre C i ω') (chunkN C i ω')
        = ∑ ω' ∈ C.atom i ω₁, C.P ω' *
            E.costOn (((List.ofFn (C.chunk ω')).take i).flatten) (C.chunk ω' ⟨i, hi⟩) := by
      refine Finset.sum_congr rfl fun ω' _ => ?_
      unfold pre chunkN
      rw [dif_pos hi]
    rw [hL, hR]
    exact hc
  · have hz : ∀ ω : C.Ω, sizeN C i ω = 0 := fun ω => by unfold sizeN; rw [dif_neg hi]
    have hz2 : ∀ ω : C.Ω, E.costOn (pre C i ω) (chunkN C i ω) = 0 := by
      intro ω
      unfold chunkN EvaderAlgorithm.costOn
      rw [dif_neg hi]
      simp
    simp [hz, hz2]

/-- Telescoping: the per-chunk costs of an evader add up to its cost on the whole
request sequence. -/
theorem sum_costOn_eq_cost (E : EvaderAlgorithm X) (ω : C.Ω) :
    ∑ i ∈ Finset.range C.m, E.costOn (pre C i ω) (chunkN C i ω) = E.cost (C.seq ω) := by
  have hstep : ∀ i, E.costOn (pre C i ω) (chunkN C i ω)
      = E.cost (pre C (i + 1) ω) - E.cost (pre C i ω) := by
    intro i
    unfold EvaderAlgorithm.costOn
    rw [pre_succ]
  rw [Finset.sum_congr rfl (fun i _ => hstep i),
    Finset.sum_range_sub (fun i => E.cost (pre C i ω)) C.m,
    pre_m, pre_zero, cost_nil, sub_zero]

/-- **The expected total size is bounded by the expected cost of any evader.** -/
theorem expTotal_le_evader_cost (E : EvaderAlgorithm X) :
    ∑ ω, C.P ω * ∑ i, C.size ω i ≤ ∑ ω, C.P ω * E.cost (C.seq ω) := by
  classical
  have h1 : ∀ ω : C.Ω, ∑ i ∈ Finset.range C.m, C.P ω * sizeN C i ω
      = C.P ω * ∑ i, C.size ω i := by
    intro ω
    rw [← Fin.sum_univ_eq_sum_range (fun i => C.P ω * sizeN C i ω) C.m, ← Finset.mul_sum]
    congr 1
    exact Finset.sum_congr rfl fun i _ => by unfold sizeN; rw [dif_pos i.2]
  have h2 : ∀ ω : C.Ω, ∑ i ∈ Finset.range C.m, C.P ω * E.costOn (pre C i ω) (chunkN C i ω)
      = C.P ω * E.cost (C.seq ω) := by
    intro ω
    rw [← Finset.mul_sum, sum_costOn_eq_cost]
  calc ∑ ω, C.P ω * ∑ i, C.size ω i
      = ∑ ω, ∑ i ∈ Finset.range C.m, C.P ω * sizeN C i ω :=
        Finset.sum_congr rfl fun ω _ => (h1 ω).symm
    _ = ∑ i ∈ Finset.range C.m, ∑ ω, C.P ω * sizeN C i ω := Finset.sum_comm
    _ ≤ ∑ i ∈ Finset.range C.m, ∑ ω, C.P ω * E.costOn (pre C i ω) (chunkN C i ω) :=
        Finset.sum_le_sum fun i _ => sum_sizeN_le_sum_costOn C E i
    _ = ∑ ω, ∑ i ∈ Finset.range C.m, C.P ω * E.costOn (pre C i ω) (chunkN C i ω) :=
        Finset.sum_comm
    _ = ∑ ω, C.P ω * E.cost (C.seq ω) := Finset.sum_congr rfl fun ω _ => h2 ω

end EvaderBound


theorem solution {X : Type*} [MetricSpace X] {s t : X}
    {cLo cHi total price : ℝ} {mL : ℕ} (C : ChunkSystemB X s t cLo cHi total price mL)
    (E : EvaderAlgorithm X) :
    ∑ ω, C.P ω * ∑ i, C.size ω i ≤ ∑ ω, C.P ω * E.cost (C.seq ω) :=
  EvaderBound.expTotal_le_evader_cost C E
