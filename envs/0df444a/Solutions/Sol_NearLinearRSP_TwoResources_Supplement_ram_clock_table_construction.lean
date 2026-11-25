-- Prove2me | solution 1 for NearLinearRSP.TwoResources.Supplement.ram_clock_table_construction
-- status  : ACCEPTED   (prove)
-- author  : @k-variant
-- created : 2026-11-25T09:22:16.006402+00:00
-- url     : https://prove2.me/submissions/b7f576be-08a2-45f4-b349-ddfb4d25cb9a

import Definitions.Def_NearLinearRSP_TwoResources_Supplement_TableMachine
import Theorems.Thm_NearLinearRSP_TwoResources_Implementation_initialization_and_expectation_correct

section

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

universe u_1

set_option autoImplicit false

set_option autoImplicit false

set_option autoImplicit false

set_option autoImplicit false
section
set_option autoImplicit false
namespace NearLinearRSP.TwoResources

theorem firstMin_mem :
  ∀ {α : Type} (f : α → ℝ) (xs : List α) (fallback : α)
    (h : xs ≠ []),
  firstMin f xs fallback ∈ xs :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.1.1.1.2.1.2.1.2.2

end NearLinearRSP.TwoResources
end

set_option autoImplicit false

set_option autoImplicit false

set_option autoImplicit false
section
set_option autoImplicit false
namespace NearLinearRSP.TwoResources.Mission.Structured

theorem run_atoms :
  ∀ (input : RAMInput) (as : List Atom) (s : Store),
  Run input (Cmd.atoms as) s (evalAtoms input as s) as.length :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.1.1.2.2.2.1.1.2.1

@[ext] theorem Store.ext :
  ∀ {s t : Store} (hnr : s.nr = t.nr)
    (hrr : s.rr = t.rr) (hnm : s.nm = t.nm) (hrm : s.rm = t.rm),
  s = t :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.1.1.2.2.2.1.2.1.1

theorem run_bounded_loop :
  ∀ (input : RAMInput) (g : Guard) (body : Cmd)
    (limit bound : ℕ) (P : ℕ → Store → Prop)
    (hguard : ∀ k s, k ≤ limit → P k s → g.eval s = decide (k < limit))
    (hstep : ∀ k s, k < limit → P k s →
      ∃ t n, Run input body s t n ∧ P (k + 1) t ∧ n ≤ bound)
    (k : ℕ) (s : Store) (hk : k ≤ limit) (hs : P k s),
  ∃ t n, Run input (.loop g body) s t n ∧ P limit t ∧
      n ≤ (bound + 2) * (limit - k) + 1 :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.1.1.2.2.2.1.2.2.1

end NearLinearRSP.TwoResources.Mission.Structured
end

set_option autoImplicit false

set_option autoImplicit false
section
set_option autoImplicit false
namespace NearLinearRSP.TwoResources.Mission.Structured

theorem Run.nat_frame :
  ∀ {input : RAMInput} {c : Cmd} {s t : Store} {n : ℕ}
    (h : Run input c s t n) (r : ℕ) (hr : r ∉ c.natWrites),
  t.nr r = s.nr r :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.1.2.1.1.1.2.2.2.2

theorem Run.real_frame :
  ∀ {input : RAMInput} {c : Cmd} {s t : Store} {n : ℕ}
    (h : Run input c s t n) (r : ℕ) (hr : r ∉ c.realWrites),
  t.rr r = s.rr r :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.1.2.1.1.2.1.1.1

theorem Run.natMemory_frame :
  ∀ {input : RAMInput} {c : Cmd} {s t : Store} {n : ℕ}
    (h : Run input c s t n) (hw : c.writesNatMemory = false),
  t.nm = s.nm :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.1.2.1.1.2.1.1.2.1

theorem Run.realMemory_frame :
  ∀ {input : RAMInput} {c : Cmd} {s t : Store} {n : ℕ}
    (h : Run input c s t n) (hw : c.writesRealMemory = false),
  t.rm = s.rm :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.1.2.1.1.2.1.1.2.2

end NearLinearRSP.TwoResources.Mission.Structured
end

set_option autoImplicit false

set_option autoImplicit false
section
set_option autoImplicit false
set_option Elab.async false
namespace NearLinearRSP.TwoResources.Mission.Queue

theorem heapTruth_leaf :
  ∀ (B : ℕ) (leaf : ℕ → Record) (v : ℕ)
    (hv : B ≤ v),
  heapTruth B leaf v = leaf v :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.1.2.1.1.2.2.2.1.2

end NearLinearRSP.TwoResources.Mission.Queue
end

set_option autoImplicit false

set_option autoImplicit false

set_option autoImplicit false

set_option autoImplicit false
section
set_option autoImplicit false
namespace NearLinearRSP.TwoResources

theorem activeVertices_edge_left :
  ∀ (I : Instance) (u v : ℕ)
    (h : (u,v) ∈ I.graph.edges),
  u ∈ activeVertices I :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.1.2.2.2.1.2.1.2.2

theorem activeVertices_edge_right :
  ∀ (I : Instance) (u v : ℕ)
    (h : (u,v) ∈ I.graph.edges),
  v ∈ activeVertices I :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.1.2.2.2.1.2.2.1.1

end NearLinearRSP.TwoResources
end

set_option autoImplicit false

set_option autoImplicit false

set_option autoImplicit false

set_option autoImplicit false

set_option autoImplicit false

set_option autoImplicit false

set_option autoImplicit false

set_option autoImplicit false
section
set_option autoImplicit false
set_option Elab.async false
namespace NearLinearRSP.TwoResources.Mission.Queue

theorem activeLeaf_at :
  ∀ (xs q : List ℕ) (key : ℕ → ℝ) (B k : ℕ)
    (hk : k<xs.length),
  activeLeaf xs q key B (B+k) =
      ⟨if slotVertex xs k∈q then k+1 else 0,key (slotVertex xs k)⟩ :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.2.2.1.1.2.1.1.2.1

theorem slotVertex_injective :
  ∀ (xs : List ℕ) (hxs : xs.Nodup) (i j : ℕ)
    (hi : i<xs.length) (hj : j<xs.length),
  slotVertex xs i=slotVertex xs j ↔ i=j :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.2.2.1.1.2.1.2.1

theorem slotVertex_idxOf_eq :
  ∀ (xs : List ℕ) (u : ℕ) (hu : u∈xs),
  slotVertex xs (xs.idxOf u)=u :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.2.2.1.1.2.2.1.2.2

theorem activeLeaf_delete_vertex :
  ∀ (xs q : List ℕ) (key : ℕ→ℝ) (B u : ℕ)
    (hxs : xs.Nodup) (hq : q.Nodup) (hu : u∈xs),
  activeLeaf xs (q.erase u) key B =
      Function.update (activeLeaf xs q key B) (B+xs.idxOf u) ⟨0,key u⟩ :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.2.2.1.1.2.2.2.1.1

theorem activeLeaf_update_vertex :
  ∀ (xs q : List ℕ) (key : ℕ→ℝ) (B u : ℕ) (value : ℝ)
    (hxs : xs.Nodup) (hu : u∈xs) (huq : u∈q),
  activeLeaf xs q (Function.update key u value) B =
      Function.update (activeLeaf xs q key B) (B+xs.idxOf u) ⟨xs.idxOf u+1,value⟩ :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.2.2.1.1.2.2.2.1.2

theorem activeLeaf_firstMin :
  ∀ (xs q : List ℕ) (key : ℕ→ℝ) (height : ℕ)
    (hxs : xs.Nodup) (hq : q.Sublist xs) (hB : xs.length≤2^height)
    (fallback : ℕ) (hne : q≠[]),
  (heapTruth (2^height) (activeLeaf xs q key (2^height)) 1).decode =
      some (vertexRecord xs key (firstMin key q fallback)) :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.2.2.1.2.1.1.1.2.2

end NearLinearRSP.TwoResources.Mission.Queue
end

set_option autoImplicit false

set_option autoImplicit false
section
set_option autoImplicit false
namespace NearLinearRSP.TwoResources.Mission.Queue
open Structured

theorem updateLeaf_refines :
  ∀ (input : RAMInput) (B : ℕ) (leaf : ℕ → Record) (s : Store)
    (hparent : ParentLayout (2 * B) s) (hone : s.nr 4 = 1)
    (hpositive : 0 < s.nr 0) (hleaf : B ≤ s.nr 0)
    (hrep : Represents B (s.nr 1) leaf s),
  ∃ out k, Run input updateLeaf s out k ∧ k ≤ 19 * Nat.clog 2 (2 * B) + 6 ∧
      out.nr 0 = 0 ∧ (∀ a, 0 < a → a < 5 → out.nr a = s.nr a) ∧
      ParentLayout (2 * B) out ∧
      Represents B (s.nr 1) (Function.update leaf (s.nr 0) ⟨s.nr 10, s.rr 2⟩) out ∧
      WinnerFrame (s.nr 1) (2 * B) s out :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.2.2.1.2.2.2.1.1

theorem buildQueue_run :
  ∀ (input : RAMInput) (B N W P R : ℕ) (s : Store)
    (hB : 0 < B) (hN : N ≤ B) (hspace : W + 2 * B ≤ P)
    (hkeys : ∀ i < N, R + i < W ∨ W + 2 * B ≤ R + i)
    (h1 : s.nr 1 = W) (h2 : s.nr 2 = P) (h3 : s.nr 3 = 0) (h4 : s.nr 4 = 1)
    (h11 : s.nr 11 = B) (h12 : s.nr 12 = N) (h13 : s.nr 13 = R),
  ∃ out cost, Run input buildQueue s out cost ∧ BuildInv B N W P R s N out ∧
      cost ≤ 15 * B + (19 * Nat.clog 2 (2 * B) + 13) * N + 3 :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.2.2.2.1.1.1.2.2.2

end NearLinearRSP.TwoResources.Mission.Queue
end

set_option autoImplicit false
section
set_option autoImplicit false
set_option Elab.async false
namespace NearLinearRSP.TwoResources.Mission.Queue

theorem activeLeaf_initial :
  ∀ (xs : List ℕ) (key : ℕ → ℝ) (B : ℕ),
  activeLeaf xs xs key B =
      prefixLeaf B (fun k => key (slotVertex xs k)) xs.length :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.2.2.2.1.1.2.1.1

end NearLinearRSP.TwoResources.Mission.Queue
end

set_option autoImplicit false
section
set_option autoImplicit false
namespace NearLinearRSP.TwoResources.Mission.Preprocess
open Structured

theorem ActiveRep.length_le :
  ∀ {n base array : ℕ} {xs : List ℕ} {s : Store}
    (h : ActiveRep n base array xs s),
  xs.length ≤ n :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.2.2.2.2.1.1.2.2.2

theorem ActiveRep.congr :
  ∀ {n base array : ℕ} {xs : List ℕ} {s t : Store}
    (h : ActiveRep n base array xs s)
    (hb : t.nr 141 = s.nr 141) (ha : t.nr 142 = s.nr 142) (hc : t.nr 143 = s.nr 143)
    (hmap : ∀ v < n, t.nm (base + v) = s.nm (base + v))
    (harray : ∀ k < xs.length, t.nm (array + k) = s.nm (array + k)),
  ActiveRep n base array xs t :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.2.2.2.2.1.2.1.1

end NearLinearRSP.TwoResources.Mission.Preprocess
end

set_option autoImplicit false

set_option autoImplicit false
section
set_option autoImplicit false
namespace NearLinearRSP.TwoResources.Mission.Preprocess
open Structured

theorem AdjacencyChain.frame :
  ∀ {mem mem' : ℕ → ℕ} {links token : ℕ} {es : List ℕ}
    (h : AdjacencyChain mem links token es)
    (hf : ∀ e ∈ es, mem' (links + e) = mem (links + e)),
  AdjacencyChain mem' links token es :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.1.1.1.1.2.1.2.2.1

end NearLinearRSP.TwoResources.Mission.Preprocess
end

set_option autoImplicit false

set_option autoImplicit false

set_option autoImplicit false

set_option autoImplicit false

set_option autoImplicit false

set_option autoImplicit false

set_option autoImplicit false
section
set_option autoImplicit false
set_option Elab.async false
namespace NearLinearRSP.TwoResources.Mission.Preprocess
open Structured

theorem outgoingIndices_lt :
  ∀ (I : Instance) (count v e : ℕ)
    (he : e ∈ outgoingIndices I count v),
  e < count :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.1.1.2.1.1.2.2.2.2

theorem outgoingIndices_edges :
  ∀ (I : Instance) (v : ℕ),
  (outgoingIndices I I.graph.edges.length v).map (edgeAt I) = (outgoingEdges I v).reverse :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.1.1.2.1.2.2.2.2.2

end NearLinearRSP.TwoResources.Mission.Preprocess
end

set_option autoImplicit false
section
set_option autoImplicit false
namespace NearLinearRSP.TwoResources.Mission.Preprocess
open Structured

theorem outgoingIndices_valid :
  ∀ (I : Instance) (u e : ℕ)
    (he : e ∈ outgoingIndices I I.graph.edges.length u),
  ∃ v, I.graph.edges[e]? = some (u,v) :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.1.1.2.2.1.1.2.2.1

end NearLinearRSP.TwoResources.Mission.Preprocess
end

set_option autoImplicit false

set_option autoImplicit false

set_option autoImplicit false
section
set_option autoImplicit false
set_option Elab.async false
namespace NearLinearRSP.TwoResources

theorem outgoingWork_erase :
  ∀ (I : Instance) (vertices : List ℕ) (u : ℕ) (hu : u ∈ vertices),
  (outgoingEdges I u).length + outgoingWork I (vertices.erase u) = outgoingWork I vertices :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.1.1.2.2.2.1.2.1.1

theorem outgoingWork_active :
  ∀ (I : Instance),
  outgoingWork I (activeVertices I) = I.graph.edges.length :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.1.1.2.2.2.1.2.2.2

end NearLinearRSP.TwoResources
end

set_option autoImplicit false

set_option autoImplicit false

set_option autoImplicit false

set_option autoImplicit false

set_option autoImplicit false

set_option autoImplicit false

set_option autoImplicit false

set_option autoImplicit false

set_option autoImplicit false

set_option autoImplicit false

set_option autoImplicit false

set_option autoImplicit false

set_option autoImplicit false

set_option autoImplicit false

set_option autoImplicit false

set_option autoImplicit false

set_option autoImplicit false

set_option autoImplicit false

set_option autoImplicit false

set_option autoImplicit false

set_option autoImplicit false

set_option autoImplicit false

set_option autoImplicit false

set_option autoImplicit false

set_option autoImplicit false

set_option autoImplicit false

set_option autoImplicit false

set_option autoImplicit false

set_option autoImplicit false

set_option autoImplicit false

set_option autoImplicit false

set_option autoImplicit false

set_option autoImplicit false

set_option autoImplicit false

set_option autoImplicit false

set_option autoImplicit false

set_option autoImplicit false

set_option autoImplicit false

set_option autoImplicit false

end

section

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

namespace NearLinearRSP.TwoResources.Supplement

theorem clockCoordinates_length_le {k : ℕ} (I : MultiInstance k) :
    (clockCoordinates I).length ≤ k := by
  simpa [clockCoordinates] using
    List.length_filter_le (fun r : Fin k => r.val = 0 ∨ 0 < coordinateBudget I 1 r)
      (List.finRange k)

theorem mem_vectors {d q : ℕ} (i : Fin d → ℕ) :
    i ∈ vectors d q ↔ ∀ r, i r < q := by
  induction d with
  | zero =>
    have h : i = fun r => Fin.elim0 r := Subsingleton.elim _ _
    simp [vectors, h]
  | succ d ih =>
    constructor
    · intro h
      obtain ⟨a, ha, hm⟩ := List.mem_flatMap.mp h
      obtain ⟨j, hj, he⟩ := List.mem_map.mp hm
      subst i
      intro r
      refine Fin.cases ?_ (fun s => ?_) r
      · simpa using List.mem_range.mp ha
      · simpa using (ih j).mp hj s
    · intro h
      apply List.mem_flatMap.mpr
      refine ⟨i 0, List.mem_range.mpr (h 0), ?_⟩
      apply List.mem_map.mpr
      refine ⟨Fin.tail i, (ih _).mpr (fun r => h r.succ), ?_⟩
      exact Fin.cons_self_tail i

theorem vectors_nodup (d q : ℕ) : (vectors d q).Nodup := by
  induction d with
  | zero => simp [vectors]
  | succ d ih =>
    rw [vectors, List.nodup_flatMap]
    constructor
    · intro a ha
      exact ih.map (Fin.cons_right_injective (α := fun _ => ℕ) a)
    · apply (List.nodup_range (n := q)).imp
      intro a b hab i hi hj
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hi
      obtain ⟨y, hy, he⟩ := List.mem_map.mp hj
      exact hab (congrArg (fun v : Fin (d + 1) → ℕ => v 0) he).symm

theorem rectangle_mem {k : ℕ} (A : ClockCall k) (i a : Fin A.d → ℕ) :
    a ∈ rectangle A i ↔ ∀ r, i r + a r < A.q := by
  classical
  simp only [rectangle, List.mem_filter, decide_eq_true_eq, mem_vectors]
  constructor
  · exact And.right
  · intro h
    exact ⟨fun r => (Nat.le_add_left _ _).trans_lt (h r), h⟩

theorem rectangle_nodup {k : ℕ} (A : ClockCall k) (i : Fin A.d → ℕ) :
    (rectangle A i).Nodup := (vectors_nodup _ _).filter _

theorem vectorIndex_cons {d : ℕ} (q a : ℕ) (i : Fin d → ℕ) :
    vectorIndex q (Fin.cons a i) = a * q ^ d + vectorIndex q i := by
  unfold vectorIndex
  rw [Fin.sum_univ_succ]
  simp only [Fin.cons_zero, Fin.val_zero, Nat.sub_zero, Nat.add_sub_cancel,
    Fin.cons_succ, Fin.val_succ]
  congr 1
  apply Finset.sum_congr rfl
  intro r hr
  congr 2
  omega

theorem vectorIndex_lt {d q : ℕ} (i : Fin d → ℕ) (hi : ∀ r, i r < q) :
    vectorIndex q i < q ^ d := by
  induction d with
  | zero => simp [vectorIndex]
  | succ d ih =>
    have ht := ih (Fin.tail i) (fun r => hi r.succ)
    have h0 := hi 0
    conv_lhs => rw [← Fin.cons_self_tail i]
    rw [vectorIndex_cons, pow_succ]
    have hmul := Nat.mul_le_mul_right (q ^ d) (Nat.succ_le_of_lt h0)
    nlinarith

theorem vectorIndex_inj {d q : ℕ} (i j : Fin d → ℕ)
    (hi : ∀ r, i r < q) (hj : ∀ r, j r < q)
    (he : vectorIndex q i = vectorIndex q j) : i = j := by
  induction d with
  | zero => exact Subsingleton.elim _ _
  | succ d ih =>
    have hi' := vectorIndex_lt (Fin.tail i) (fun r => hi r.succ)
    have hj' := vectorIndex_lt (Fin.tail j) (fun r => hj r.succ)
    have he' : i 0 * q ^ d + vectorIndex q (Fin.tail i) =
        j 0 * q ^ d + vectorIndex q (Fin.tail j) := by
      simpa only [← vectorIndex_cons, Fin.cons_self_tail] using he
    have h0 : i 0 = j 0 := by
      rcases lt_trichotomy (i 0) (j 0) with h | h | h
      · have hh := Nat.mul_le_mul_right (q ^ d) (Nat.succ_le_of_lt h)
        nlinarith
      · exact h
      · have hh := Nat.mul_le_mul_right (q ^ d) (Nat.succ_le_of_lt h)
        nlinarith
    have ht : Fin.tail i = Fin.tail j := ih _ _ (fun r => hi r.succ)
      (fun r => hj r.succ) (by rw [h0] at he'; omega)
    rw [← Fin.cons_self_tail i, ← Fin.cons_self_tail j, h0, ht]

theorem put_same {d : ℕ} (T : MultiTable d) (v : ℕ) (i : Fin d → ℕ) (c : MultiCell) :
    put T v i c v i = c := by simp [put]

theorem put_other {d : ℕ} (T : MultiTable d) (v w : ℕ) (i j : Fin d → ℕ)
    (c : MultiCell) (h : w ≠ v ∨ j ≠ i) : put T v i c w j = T w j := by
  simp only [put]
  exact if_neg (by tauto)

theorem value_of_valid {k : ℕ} (A : ClockCall k) (T : MultiTable A.d)
    (v : ℕ) (i : Fin A.d → ℕ) (hi : ∀ r, i r < A.q) :
    value A T v i = (T v i).value := by
  simp only [value]
  exact if_neg (by simpa using hi)

theorem selectMin_fold_mem {α : Type} (f : α → ℝ) (xs : List α) (a : α) :
    xs.foldl (fun x y => if f y < f x then y else x) a ∈ a :: xs := by
  induction xs generalizing a with
  | nil => simp
  | cons x xs ih =>
    simp only [List.foldl_cons]
    split_ifs with h
    · have hm := ih x
      simp only [List.mem_cons] at hm ⊢
      tauto
    · have hm := ih a
      simp only [List.mem_cons] at hm ⊢
      tauto

theorem selectMin_mem {α : Type} (f : α → ℝ) (xs : List α) (a : α) (h : xs ≠ []) :
    selectMin f xs a ∈ xs := by
  cases xs with
  | nil => exact (h rfl).elim
  | cons x xs =>
    simpa [selectMin, List.foldl_cons] using selectMin_fold_mem f xs x

theorem incident_valid {k : ℕ} (I : MultiInstance k) (v : ℕ)
    (hv : v ∈ incidentVertices I) : v < I.graph.n := by
  simp only [incidentVertices, List.mem_eraseDups, List.mem_cons] at hv
  rcases hv with rfl | hv
  · exact I.source_valid
  · obtain ⟨e, he, hv⟩ := List.mem_flatMap.mp hv
    have hb := I.graph.endpoints e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl
    · exact hb.1
    · exact hb.2

end NearLinearRSP.TwoResources.Supplement

end

section

set_option autoImplicit false
open scoped BigOperators

namespace NearLinearRSP.TwoResources.Supplement

theorem range_blocks (rows width : ℕ) :
    (List.range rows).flatMap (fun r => (List.range width).map (r * width + ·)) =
      List.range (rows * width) := by
  induction rows with
  | zero => simp
  | succ rows ih =>
    rw [List.range_succ, List.flatMap_append, ih, Nat.succ_mul, List.range_add]
    simp

theorem vectorIndices_in_order (d q : ℕ) :
    ((vectors d q).map (vectorIndex q)) = List.range (q ^ d) := by
  induction d with
  | zero => simp [vectors, vectorIndex, List.range_one]
  | succ d ih =>
    rw [vectors, List.map_flatMap]
    have he (a : ℕ) : (((vectors d q).map (Fin.cons a)).map (vectorIndex q)) =
        (List.range (q ^ d)).map (a * q ^ d + ·) := by
      rw [← ih]
      simp only [List.map_map, Function.comp_def, vectorIndex_cons]
    simp only [he, pow_succ', range_blocks]

theorem vectorIndex_add {d : ℕ} (q : ℕ) (i a : Fin d → ℕ) :
    vectorIndex q (fun r => i r + a r) = vectorIndex q i + vectorIndex q a := by
  simp only [vectorIndex, Nat.add_mul, Finset.sum_add_distrib]

theorem scanAddress_add {d : ℕ} (base n q v : ℕ) (i a : Fin d → ℕ) :
    scanAddress base n q v (fun r => i r + a r) =
      scanAddress base n q v i + vectorIndex q a * ((d + 4) * n) := by
  simp only [scanAddress, vectorIndex_add]
  ring

noncomputable def keepCandidate {α : Type} (f : α → ℝ) (old : Option α) (a : α) : Option α :=
  match old with
  | none => some a
  | some b => some (if f a < f b then a else b)

theorem fold_candidates_some {α : Type} (f : α → ℝ) (xs : List α) (b : α) :
    xs.foldl (keepCandidate f) (some b) =
      some (xs.foldl (fun w a => if f a < f w then a else w) b) := by
  induction xs generalizing b with
  | nil => rfl
  | cons a xs ih => simpa only [List.foldl_cons, keepCandidate] using ih (if f a < f b then a else b)

theorem candidate_choice {α : Type} (f : α → ℝ) (a : α) (xs : List α) :
    (a :: xs).foldl (keepCandidate f) none = some (selectMin f (a :: xs) a) := by
  simp [selectMin, List.foldl_cons, keepCandidate, fold_candidates_some]

end NearLinearRSP.TwoResources.Supplement

end

section

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

namespace NearLinearRSP.TwoResources.Supplement

theorem fold_preserves {α β : Type*} (f : β → α → β) (P : β → Prop)
    (xs : List α) (b : β) (hb : P b)
    (hf : ∀ a ∈ xs, ∀ b, P b → P (f b a)) : P (xs.foldl f b) := by
  induction xs generalizing b with
  | nil => exact hb
  | cons a xs ih =>
    apply ih (f b a) (hf a (by simp) b hb)
    intro c hc U hU
    exact hf c (by simp [hc]) U hU

noncomputable def settle {d : ℕ} (S : MultiLayer d) (u : ℕ) (i : Fin d → ℕ) : MultiLayer d :=
  { S with
    table := put S.table u i ⟨S.keys u, S.parents u, S.nextRank⟩
    queue := S.queue.erase u
    nextRank := S.nextRank + 1 }

noncomputable def relaxAll {k : ℕ} (A : ClockCall k) (i : Fin A.d → ℕ)
    (u : ℕ) (S : MultiLayer A.d) : MultiLayer A.d :=
  (callEdges A).foldl (relax A i u) S

noncomputable def picked {k : ℕ} (A : ClockCall k) (S : MultiLayer A.d) : ℕ :=
  selectMin S.keys S.queue A.I.source

noncomputable def runQueue {k : ℕ} (A : ClockCall k) (i : Fin A.d → ℕ)
    (n : ℕ) (S : MultiLayer A.d) : MultiLayer A.d :=
  (List.range n).foldl (fun S _ => pop A i S) S

theorem runQueue_zero {k : ℕ} (A : ClockCall k) (i : Fin A.d → ℕ)
    (S : MultiLayer A.d) : runQueue A i 0 S = S := rfl

theorem runQueue_succ {k : ℕ} (A : ClockCall k) (i : Fin A.d → ℕ)
    (n : ℕ) (S : MultiLayer A.d) : runQueue A i (n + 1) S = pop A i (runQueue A i n S) := by
  simp [runQueue, List.range_succ, List.foldl_append]

theorem relax_table {k : ℕ} (A : ClockCall k) (i : Fin A.d → ℕ) (u : ℕ)
    (S : MultiLayer A.d) (e : ℕ × ℕ) : (relax A i u S e).table = S.table := by
  unfold relax
  dsimp only
  split_ifs <;> rfl

theorem relax_queue {k : ℕ} (A : ClockCall k) (i : Fin A.d → ℕ) (u : ℕ)
    (S : MultiLayer A.d) (e : ℕ × ℕ) : (relax A i u S e).queue = S.queue := by
  unfold relax
  dsimp only
  split_ifs <;> rfl

theorem relax_nextRank {k : ℕ} (A : ClockCall k) (i : Fin A.d → ℕ) (u : ℕ)
    (S : MultiLayer A.d) (e : ℕ × ℕ) : (relax A i u S e).nextRank = S.nextRank := by
  unfold relax
  dsimp only
  split_ifs <;> rfl

theorem relaxAll_table {k : ℕ} (A : ClockCall k) (i : Fin A.d → ℕ) (u : ℕ)
    (S : MultiLayer A.d) : (relaxAll A i u S).table = S.table := by
  apply fold_preserves (relax A i u) (fun U => U.table = S.table) _ S rfl
  intro e he U hU
  exact (relax_table A i u U e).trans hU

theorem relaxAll_queue {k : ℕ} (A : ClockCall k) (i : Fin A.d → ℕ) (u : ℕ)
    (S : MultiLayer A.d) : (relaxAll A i u S).queue = S.queue := by
  apply fold_preserves (relax A i u) (fun U => U.queue = S.queue) _ S rfl
  intro e he U hU
  exact (relax_queue A i u U e).trans hU

theorem relaxAll_nextRank {k : ℕ} (A : ClockCall k) (i : Fin A.d → ℕ) (u : ℕ)
    (S : MultiLayer A.d) : (relaxAll A i u S).nextRank = S.nextRank := by
  apply fold_preserves (relax A i u) (fun U => U.nextRank = S.nextRank) _ S rfl
  intro e he U hU
  exact (relax_nextRank A i u U e).trans hU

theorem picked_mem {k : ℕ} (A : ClockCall k) (S : MultiLayer A.d) (h : S.queue ≠ []) :
    picked A S ∈ S.queue := selectMin_mem _ _ _ h

theorem pop_of_nonempty {k : ℕ} (A : ClockCall k) (i : Fin A.d → ℕ)
    (S : MultiLayer A.d) (h : S.queue ≠ []) :
    pop A i S = relaxAll A i (picked A S) (settle S (picked A S) i) := by
  unfold pop
  cases he : S.queue with
  | nil => exact (h he).elim
  | cons v vs => simp [relaxAll, settle, picked, selectMin, he]

theorem pop_queue_length {k : ℕ} (A : ClockCall k) (i : Fin A.d → ℕ)
    (S : MultiLayer A.d) : (pop A i S).queue.length = S.queue.length - 1 := by
  by_cases h : S.queue = []
  · simp [pop, h]
  · rw [pop_of_nonempty A i S h, relaxAll_queue]
    exact List.length_erase_of_mem (picked_mem A S h)

theorem pop_queue_sublist {k : ℕ} (A : ClockCall k) (i : Fin A.d → ℕ)
    (S : MultiLayer A.d) : (pop A i S).queue.Sublist S.queue := by
  by_cases h : S.queue = []
  · simp [pop, h]
  · rw [pop_of_nonempty A i S h, relaxAll_queue]
    exact List.erase_sublist

theorem runQueue_queue_length {k : ℕ} (A : ClockCall k) (i : Fin A.d → ℕ)
    (n : ℕ) (S : MultiLayer A.d) : (runQueue A i n S).queue.length = S.queue.length - n := by
  induction n with
  | zero => simp [runQueue]
  | succ n ih => rw [runQueue_succ, pop_queue_length, ih]; omega

theorem runQueue_queue_sublist {k : ℕ} (A : ClockCall k) (i : Fin A.d → ℕ)
    (n : ℕ) (S : MultiLayer A.d) : (runQueue A i n S).queue.Sublist S.queue := by
  induction n with
  | zero => exact List.Sublist.refl _
  | succ n ih => rw [runQueue_succ]; exact (pop_queue_sublist A i _).trans ih

theorem constructLayer_queue_empty {k : ℕ} (A : ClockCall k) (T : MultiTable A.d)
    (i : Fin A.d → ℕ) :
    (runQueue A i (incidentVertices A.I).length (initializeLayer A T i)).queue = [] := by
  apply List.length_eq_zero_iff.mp
  rw [runQueue_queue_length]
  simp [initializeLayer]

theorem pop_other_index {k : ℕ} (A : ClockCall k) (i j : Fin A.d → ℕ)
    (S : MultiLayer A.d) (v : ℕ) (hij : j ≠ i) :
    (pop A i S).table v j = S.table v j := by
  by_cases h : S.queue = []
  · simp [pop, h]
  · rw [pop_of_nonempty A i S h, relaxAll_table]
    exact put_other _ _ _ _ _ _ (Or.inr hij)

theorem runQueue_other_index {k : ℕ} (A : ClockCall k) (i j : Fin A.d → ℕ)
    (n : ℕ) (S : MultiLayer A.d) (v : ℕ) (hij : j ≠ i) :
    (runQueue A i n S).table v j = S.table v j := by
  induction n with
  | zero => rfl
  | succ n ih => rw [runQueue_succ]; exact (pop_other_index A i j _ v hij).trans ih

theorem constructLayer_other_index {k : ℕ} (A : ClockCall k) (T : MultiTable A.d)
    (i j : Fin A.d → ℕ) (v : ℕ) (hij : j ≠ i) :
    constructLayer A T i v j = T v j :=
  runQueue_other_index A i j _ _ v hij

end NearLinearRSP.TwoResources.Supplement

end

section

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 800000

namespace NearLinearRSP.TwoResources.Supplement

theorem expectation_congr {k : ℕ} (A : ClockCall k) (T U : MultiTable A.d)
    (u v : ℕ) (i : Fin A.d → ℕ)
    (h : ∀ a ∈ rectangle A i,
      value A T u (fun r => i r + a r) = value A U u (fun r => i r + a r)) :
    expectation A T u v i = expectation A U u v i := by
  unfold expectation
  dsimp only
  congr 1
  apply congrArg List.sum
  apply List.map_congr_left
  intro a ha
  rw [h a ha]

theorem value_congr_vertex {k : ℕ} (A : ClockCall k) (T U : MultiTable A.d)
    (u : ℕ) (i : Fin A.d → ℕ) (h : T u i = U u i) :
    value A T u i = value A U u i := by
  unfold value
  rw [h]

end NearLinearRSP.TwoResources.Supplement

end

section

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000

namespace NearLinearRSP.TwoResources.Supplement

theorem incident_nodup {k : ℕ} (I : MultiInstance k) : (incidentVertices I).Nodup := by
  exact activeVertices_nodup (lengthInstance I)

end NearLinearRSP.TwoResources.Supplement

end

section

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000

namespace NearLinearRSP.TwoResources.Supplement

theorem expectation_settle_other {k : ℕ} (A : ClockCall k)
    (i : Fin A.d → ℕ) (S : MultiLayer A.d) (u w v : ℕ) (hwu : w ≠ u) :
    expectation A (settle S u i).table w v i = expectation A S.table w v i := by
  apply expectation_congr
  intro a ha
  exact value_congr_vertex A _ _ w _ (put_other _ _ _ _ _ _ (Or.inl hwu))

end NearLinearRSP.TwoResources.Supplement

end

section

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000

namespace NearLinearRSP.TwoResources.Supplement

def KeyParent {k : ℕ} (A : ClockCall k) (i : Fin A.d → ℕ)
    (S : MultiLayer A.d) (v : ℕ) : Prop :=
  match S.parents v with
  | .none => v = A.I.source ∨ S.keys v = 1
  | .tick j => ∃ h : j < A.d,
      S.keys v = value A S.table v (Function.update i ⟨j, h⟩ (i ⟨j, h⟩ + 1))
  | .edge u => (u, v) ∈ callEdges A ∧ u ∈ incidentVertices A.I ∧ u ∉ S.queue ∧
      S.keys v = expectation A S.table u v i

structure LayerParents {k : ℕ} (A : ClockCall k) (i : Fin A.d → ℕ)
    (S : MultiLayer A.d) : Prop where
  valid : ∀ v ∈ incidentVertices A.I, KeyParent A i S v
  sync : ∀ v ∈ incidentVertices A.I, v ∉ S.queue → (S.table v i).parent = S.parents v
  rank : ∀ v ∈ incidentVertices A.I, v ∉ S.queue → (S.table v i).rank < S.nextRank
  before : ∀ v ∈ incidentVertices A.I, v ∉ S.queue → ∀ u, S.parents v = .edge u →
    (S.table u i).rank < (S.table v i).rank

theorem initializeLayer_parents {k : ℕ} (A : ClockCall k) (T : MultiTable A.d)
    (i : Fin A.d → ℕ) : LayerParents A i (initializeLayer A T i) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro v hv
    by_cases hs : v = A.I.source
    · simp [KeyParent, initializeLayer, hs]
    · cases ht : nextTick A T v i with
      | none => simp [KeyParent, initializeLayer, hs, ht]
      | some r =>
        simp only [KeyParent, initializeLayer, if_neg hs, ht]
        exact ⟨r.isLt, trivial⟩
  · intro v hv hn; exact (hn hv).elim
  · intro v hv hn; exact (hn hv).elim
  · intro v hv hn; exact (hn hv).elim

theorem tick_index_ne {d : ℕ} (i : Fin d → ℕ) (r : Fin d) :
    Function.update i r (i r + 1) ≠ i := by
  intro h
  have hh := congrFun h r
  simp at hh

theorem settle_keyParent {k : ℕ} (A : ClockCall k) (i : Fin A.d → ℕ)
    (S : MultiLayer A.d) (u v : ℕ) (hu : u ∈ S.queue)
    (h : KeyParent A i S v) : KeyParent A i (settle S u i) v := by
  unfold KeyParent at h ⊢
  change (match S.parents v with
    | .none => _
    | .tick j => _
    | .edge w => _)
  cases hp : S.parents v with
  | none => simpa [hp, settle] using h
  | tick j =>
    rw [hp] at h
    obtain ⟨hj, he⟩ := h
    refine ⟨hj, ?_⟩
    change S.keys v = value A (settle S u i).table v _
    have hf : (settle S u i).table v (Function.update i ⟨j, hj⟩ (i ⟨j, hj⟩ + 1)) =
        S.table v (Function.update i ⟨j, hj⟩ (i ⟨j, hj⟩ + 1)) :=
      put_other S.table u v i _ _ (Or.inr (tick_index_ne i ⟨j, hj⟩))
    rw [value_congr_vertex A _ S.table v _ hf]
    exact he
  | edge w =>
    rw [hp] at h
    have hwu : w ≠ u := fun he => h.2.2.1 (he.symm ▸ hu)
    refine ⟨h.1, h.2.1, ?_, ?_⟩
    · exact fun hm => h.2.2.1 (List.mem_of_mem_erase hm)
    · change S.keys v = expectation A (settle S u i).table w v i
      rw [expectation_settle_other A i S u w v hwu]
      exact h.2.2.2

theorem settle_parents {k : ℕ} (A : ClockCall k) (i : Fin A.d → ℕ)
    (S : MultiLayer A.d) (hS : LayerParents A i S)
    (u : ℕ) (hu : u ∈ S.queue) (huv : u ∈ incidentVertices A.I) :
    LayerParents A i (settle S u i) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro v hv
    exact settle_keyParent A i S u v hu (hS.valid v hv)
  · intro v hv hn
    by_cases h : v = u
    · subst v; simp [settle, put_same]
    · have hn' : v ∉ S.queue := fun hm => hn ((List.mem_erase_of_ne h).mpr hm)
      change (put S.table u i _ v i).parent = S.parents v
      rw [put_other _ _ _ _ _ _ (Or.inl h)]
      exact hS.sync v hv hn'
  · intro v hv hn
    by_cases h : v = u
    · subst v; simp [settle, put_same]
    · have hn' : v ∉ S.queue := fun hm => hn ((List.mem_erase_of_ne h).mpr hm)
      change (put S.table u i _ v i).rank < S.nextRank + 1
      rw [put_other _ _ _ _ _ _ (Or.inl h)]
      exact (hS.rank v hv hn').trans (Nat.lt_succ_self _)
  · intro v hv hn w hp
    have hp' : S.parents v = .edge w := hp
    have hvalid := hS.valid v hv
    unfold KeyParent at hvalid
    rw [hp'] at hvalid
    have hwu : w ≠ u := fun he => hvalid.2.2.1 (he.symm ▸ hu)
    change (put S.table u i _ w i).rank < (put S.table u i _ v i).rank
    rw [put_other _ _ _ _ _ _ (Or.inl hwu)]
    by_cases h : v = u
    · subst v
      rw [put_same]
      exact hS.rank w hvalid.2.1 hvalid.2.2.1
    · rw [put_other _ _ _ _ _ _ (Or.inl h)]
      have hn' : v ∉ S.queue := fun hm => hn ((List.mem_erase_of_ne h).mpr hm)
      exact hS.before v hv hn' w hp'

theorem relax_parents_outside {k : ℕ} (A : ClockCall k) (i : Fin A.d → ℕ)
    (u : ℕ) (S : MultiLayer A.d) (e : ℕ × ℕ) (v : ℕ) (hv : v ∉ S.queue) :
    (relax A i u S e).parents v = S.parents v := by
  unfold relax
  dsimp only
  split_ifs with he hb
  · have hne : v ≠ e.2 := by intro h; exact hv (h.symm ▸ he.2)
    simp [Function.update_of_ne hne]
  · rfl
  · rfl

theorem relax_parents {k : ℕ} (A : ClockCall k) (i : Fin A.d → ℕ)
    (S : MultiLayer A.d) (hS : LayerParents A i S) (u : ℕ)
    (hu : u ∈ incidentVertices A.I) (hun : u ∉ S.queue)
    (e : ℕ × ℕ) (he : e ∈ callEdges A) : LayerParents A i (relax A i u S e) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro v hv
    unfold relax
    dsimp only
    split_ifs with hc hb
    · by_cases hve : v = e.2
      · subst v
        simp only [KeyParent, Function.update_self]
        exact ⟨by simpa only [hc.1] using (show (e.1, e.2) ∈ callEdges A from he), hu, hun, trivial⟩
      · have hvp := hS.valid v hv
        simpa only [KeyParent, Function.update_of_ne hve] using hvp
    · exact hS.valid v hv
    · exact hS.valid v hv
  · intro v hv hn
    rw [relax_queue] at hn
    rw [relax_table, relax_parents_outside A i u S e v hn]
    exact hS.sync v hv hn
  · intro v hv hn
    rw [relax_queue] at hn
    rw [relax_table, relax_nextRank]
    exact hS.rank v hv hn
  · intro v hv hn w hp
    rw [relax_queue] at hn
    rw [relax_parents_outside A i u S e v hn] at hp
    rw [relax_table]
    exact hS.before v hv hn w hp

theorem relaxAll_parents {k : ℕ} (A : ClockCall k) (i : Fin A.d → ℕ)
    (S : MultiLayer A.d) (hS : LayerParents A i S) (u : ℕ)
    (hu : u ∈ incidentVertices A.I) (hun : u ∉ S.queue) :
    LayerParents A i (relaxAll A i u S) := by
  have hh : LayerParents A i (relaxAll A i u S) ∧ u ∉ (relaxAll A i u S).queue := by
    apply fold_preserves (relax A i u) (fun U => LayerParents A i U ∧ u ∉ U.queue)
      (callEdges A) S ⟨hS, hun⟩
    intro e he U hU
    refine ⟨relax_parents A i U hU.1 u hu hU.2 e he, ?_⟩
    rw [relax_queue]; exact hU.2
  exact hh.1

theorem pop_parents {k : ℕ} (A : ClockCall k) (i : Fin A.d → ℕ)
    (S : MultiLayer A.d) (hS : LayerParents A i S) (hnodup : S.queue.Nodup)
    (hsub : ∀ v ∈ S.queue, v ∈ incidentVertices A.I) : LayerParents A i (pop A i S) := by
  by_cases hn : S.queue = []
  · simpa [pop, hn] using hS
  · rw [pop_of_nonempty A i S hn]
    have hu := picked_mem A S hn
    exact relaxAll_parents A i _ (settle_parents A i S hS _ hu (hsub _ hu))
      _ (hsub _ hu) hnodup.not_mem_erase

theorem runQueue_parents {k : ℕ} (A : ClockCall k) (i : Fin A.d → ℕ)
    (n : ℕ) (S : MultiLayer A.d) (hS : LayerParents A i S) (hnodup : S.queue.Nodup)
    (hsub : ∀ v ∈ S.queue, v ∈ incidentVertices A.I) :
    LayerParents A i (runQueue A i n S) := by
  induction n with
  | zero => exact hS
  | succ n ih =>
    rw [runQueue_succ]
    have hss := runQueue_queue_sublist A i n S
    exact pop_parents A i _ ih (hnodup.sublist hss) (fun v hv => hsub v (hss.subset hv))

end NearLinearRSP.TwoResources.Supplement

end

section

set_option autoImplicit false
set_option maxHeartbeats 1000000
open scoped BigOperators

namespace NearLinearRSP.TwoResources.Supplement.TableQuery
open Mission.Structured

theorem scanAddress_tick {d : ℕ} (base n q v : ℕ) (i : Fin d → ℕ) (r : Fin d) :
    scanAddress base n q v (Function.update i r (i r + 1)) =
      scanAddress base n q v i + stride n q r := by
  let e : Fin d → ℕ := fun x => if x = r then 1 else 0
  have h : Function.update i r (i r + 1) = fun x => i x + e x := by
    funext x
    by_cases hx : x = r
    · subst x; simp [e]
    · simp [e, hx]
  have he : vectorIndex q e = q ^ (d - 1 - r.val) := by simp [vectorIndex, e, ite_mul]
  rw [h, scanAddress_add, he]
  simp only [stride]; ring

end NearLinearRSP.TwoResources.Supplement.TableQuery

end

section

set_option autoImplicit false

namespace NearLinearRSP.TwoResources.Supplement.TableQuery
open Mission.Structured

def added (dst src n : ℕ) (s : Store) : Store :=
  {s with nr := Function.update s.nr dst (s.nr dst + n * s.nr src)}

theorem add_copies_run (input : RAMInput) (dst src : ℕ) (h : src ≠ dst) (n : ℕ) (s : Store) :
    Run input (addCopies dst src n) s (added dst src n s) n := by
  induction n with
  | zero => simpa [addCopies, added] using Run.skip (input := input) s
  | succ n ih =>
    let a : Atom := ⟨.natOp .add dst dst src, trivial⟩
    have he : a.eval input (added dst src n s) = added dst src (n + 1) s := by
      simp [a, added, Atom.eval, Store.ofRAM, Store.at, ramStep, evalNat, Function.update_of_ne h,
        Function.update_idem, Nat.succ_mul, Nat.add_assoc]
    exact Run.seq ih (he ▸ Run.atom a _)

theorem state_large (r : ℕ) : 100 ≤ stateReg r := by unfold stateReg CandidateRAM.current; omega
theorem state_inj {i j : ℕ} : stateReg i = stateReg j ↔ i = j := by
  unfold stateReg CandidateRAM.current; omega

end NearLinearRSP.TwoResources.Supplement.TableQuery

end

section

set_option autoImplicit false
set_option maxHeartbeats 1500000

namespace NearLinearRSP.TwoResources.Supplement.TableQuery
open Mission.Structured

def partialProduct (s : Store) (j : ℕ) : Store :=
  {s with nr := Function.update (Function.update s.nr 62 (j * s.nr 58)) 61 j}

theorem product_step (input : RAMInput) (s : Store) (j : ℕ) (hone : s.nr 31 = 1) :
    Run input (.atoms productBody) (partialProduct s j) (partialProduct s (j + 1)) 2 := by
  have he : evalAtoms input productBody (partialProduct s j) = partialProduct s (j + 1) := by
    apply Store.ext
    · funext r
      by_cases h61 : r = 61 <;> by_cases h62 : r = 62 <;>
        simp [productBody, partialProduct, evalAtoms, Atom.eval, Store.ofRAM, ramStep, Store.at,
          evalNat, h61, h62, hone, Nat.succ_mul]
    · rfl
    · rfl
    · rfl
  exact he ▸ run_atoms input productBody (partialProduct s j)

theorem product_loop_run (input : RAMInput) (s : Store) (hone : s.nr 31 = 1)
    (remaining j : ℕ) (hend : j + remaining = s.nr 57) :
    Run input productLoop (partialProduct s j) (partialProduct s (s.nr 57)) (4 * remaining + 1) := by
  induction remaining generalizing j with
  | zero =>
    have he : j = s.nr 57 := by omega
    subst j
    exact Run.loopFalse (by simp [Guard.eval, natTest, partialProduct])
  | succ n ih =>
    have hg : (Guard.nat .lt 61 57).eval (partialProduct s j) = true := by
      simp [Guard.eval, natTest, partialProduct, show j < s.nr 57 by omega]
    have ht := ih (j + 1) (by omega)
    have hx := Run.loopTrue hg (product_step input s j hone) ht
    simpa only [productLoop, show 1 + 2 + 1 + (4 * n + 1) = 4 * (n + 1) + 1 by omega] using hx

def productResult (s : Store) : Store :=
  let p := partialProduct s (s.nr 57)
  {p with nr := Function.update p.nr 58 (s.nr 57 * s.nr 58)}

theorem product_run (input : RAMInput) (s : Store) (hone : s.nr 31 = 1) :
    Run input productCmd s (productResult s) (4 * s.nr 57 + 4) := by
  have h0 : evalAtoms input productInit s = partialProduct s 0 := by
    simp [evalAtoms, productInit, Atom.eval, Store.ofRAM, ramStep, Store.at, partialProduct]
  have hf : productLast.eval input (partialProduct s (s.nr 57)) = productResult s := by
    simp [productResult, partialProduct, productLast, Atom.eval, Store.ofRAM, ramStep, Store.at]
  have he := Run.seq (h0 ▸ run_atoms input productInit s)
    (Run.seq (product_loop_run input s hone (s.nr 57) 0 (by omega)) (hf ▸ Run.atom productLast _))
  simpa only [productInit, List.length_cons, List.length_nil, productCmd,
    show 2 + (4 * s.nr 57 + 1 + 1) = 4 * s.nr 57 + 4 by omega] using he

def recorded (s : Store) (r : ℕ) : Store := {s with nr := Function.update s.nr (strideReg r) (s.nr 58)}

theorem stride_large (r : ℕ) : 100 ≤ strideReg r := by unfold strideReg CandidateRAM.current; omega
theorem stride_inj {i j : ℕ} : strideReg i = strideReg j ↔ i = j := by
  unfold strideReg CandidateRAM.current; omega

theorem record_run (input : RAMInput) (s : Store) (r : ℕ) (hone : s.nr 31 = 1) :
    let t := productResult (recorded s r)
    Run input (recordCmd r) s t (4 * s.nr 57 + 5) ∧ t.nr 58 = s.nr 57 * s.nr 58 ∧
      t.nr (strideReg r) = s.nr 58 ∧
      (∀ j, j ≠ strideReg r → j ≠ 58 → j ≠ 61 → j ≠ 62 → t.nr j = s.nr j) ∧
      t.rr = s.rr ∧ t.nm = s.nm ∧ t.rm = s.rm := by
  let p := recorded s r
  have hh := stride_large r
  have h31 : 31 ≠ strideReg r := by omega
  have h57 : 57 ≠ strideReg r := by omega
  have h58 : 58 ≠ strideReg r := by omega
  have hp : Run input (.atom (recordStride r)) s p 1 := Run.atom _ _
  have ht := product_run input p (by simpa [p, recorded, Function.update_of_ne h31] using hone)
  refine ⟨?_, ?_, ?_, ?_, rfl, rfl, rfl⟩
  · have he : 1 + (4 * p.nr 57 + 4) = 4 * s.nr 57 + 5 := by
      simp [p, recorded, Function.update_of_ne h57]; omega
    exact he ▸ Run.seq hp ht
  · simp [productResult, recorded, Function.update_of_ne h57, Function.update_of_ne h58]
  · simp [productResult, recorded, partialProduct, Function.update_of_ne h58.symm,
      Function.update_of_ne (show strideReg r ≠ 61 by omega),
      Function.update_of_ne (show strideReg r ≠ 62 by omega)]
  · intro j hs h₈ h₁ h₂
    simp [productResult, recorded, partialProduct, Function.update_of_ne hs,
      Function.update_of_ne h₈, Function.update_of_ne h₁, Function.update_of_ne h₂]

theorem powers_run (input : RAMInput) (s : Store) (d : ℕ) (hone : s.nr 31 = 1) :
    ∃ t, Run input (powers d) s t (d * (4 * s.nr 57 + 5)) ∧
      t.nr 58 = s.nr 58 * s.nr 57 ^ d ∧
      (∀ r < d, t.nr (strideReg r) = s.nr 58 * s.nr 57 ^ (d - 1 - r)) ∧
      (∀ j, (∀ r < d, j ≠ strideReg r) → j ≠ 58 → j ≠ 61 → j ≠ 62 → t.nr j = s.nr j) ∧
      t.rr = s.rr ∧ t.nm = s.nm ∧ t.rm = s.rm := by
  induction d generalizing s with
  | zero =>
    refine ⟨s, by simpa [powers] using Run.skip (input := input) s, by simp,
      by simp, fun _ _ _ _ _ => rfl, rfl, rfl, rfl⟩
  | succ d ih =>
    let p := productResult (recorded s d)
    obtain ⟨hrun, hp, hs, hf, hrr, hnm, hrm⟩ := record_run input s d hone
    have hg := stride_large d
    have h31 : p.nr 31 = s.nr 31 := hf 31 (by omega) (by decide) (by decide) (by decide)
    have h57 : p.nr 57 = s.nr 57 := hf 57 (by omega) (by decide) (by decide) (by decide)
    obtain ⟨t, ht, htval, hslots, hrest, tr, tn, tm⟩ := ih p (h31.trans hone)
    rw [h57] at ht htval hslots
    have hpc : p.nr 58 = s.nr 57 * s.nr 58 := hp
    rw [hpc] at htval hslots
    refine ⟨t, ?_, ?_, ?_, ?_, tr.trans hrr, tn.trans hnm, tm.trans hrm⟩
    · have hc : 4 * s.nr 57 + 5 + d * (4 * s.nr 57 + 5) = (d + 1) * (4 * s.nr 57 + 5) := by ring
      exact hc ▸ Run.seq hrun ht
    · rw [htval, pow_succ]; ring
    · intro r hr
      by_cases he : r = d
      · subst r
        have hh := hrest (strideReg d) (fun j hj h => by have := stride_inj.mp h; omega)
          (by omega) (by omega) (by omega)
        simpa using hh.trans hs
      · have hj : r < d := by omega
        have hn : d + 1 - 1 - r = (d - 1 - r) + 1 := by omega
        rw [hn, pow_succ, hslots r hj]
        ring
    · intro j hne h₈ h₁ h₂
      exact (hrest j (fun r hr => hne r (by omega)) h₈ h₁ h₂).trans
        (hf j (hne d (by omega)) h₈ h₁ h₂)

end NearLinearRSP.TwoResources.Supplement.TableQuery

end

section

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace NearLinearRSP.TwoResources.Supplement.TableQuery
open Mission.Structured
open Mission.Query (prependResult)

theorem scanAddress_inside {k : ℕ} (A : ClockCall k) (base v : ℕ) (hv : v < A.I.graph.n)
    (i : Fin A.d → ℕ) (hi : ∀ r, i r < A.q) (x : ℕ) (hx : x < A.d + 4) :
    scanAddress base A.I.graph.n A.q v i + x < extent A base := by
  have hr := vectorIndex_lt i hi
  have hm := Nat.mul_le_mul_right A.I.graph.n (Nat.succ_le_of_lt hr)
  rw [Nat.succ_mul] at hm
  have hrow : vectorIndex A.q i * A.I.graph.n + v + 1 ≤ A.q ^ A.d * A.I.graph.n := by omega
  have hn := Nat.mul_le_mul_left (A.d + 4) hrow
  rw [Nat.mul_add, Nat.mul_one] at hn
  unfold scanAddress extent
  have he : (A.d + 4) * A.I.graph.n * A.q ^ A.d = (A.d + 4) * (A.q ^ A.d * A.I.graph.n) := by ring
  rw [he]; omega

end NearLinearRSP.TwoResources.Supplement.TableQuery

end

section

set_option autoImplicit false
set_option maxHeartbeats 1400000

namespace NearLinearRSP.TwoResources.Supplement.LayerRAM
open Mission.Structured TableQuery

noncomputable def nextValue {k : ℕ} (A : ClockCall k) (T : MultiTable A.d) (v : ℕ)
    (i : Fin A.d → ℕ) (r : Fin A.d) := value A T v (Function.update i r (i r + 1))

structure Neighbors {k : ℕ} (A : ClockCall k) (T : MultiTable A.d) (v : ℕ) (i : Fin A.d → ℕ) (s : Store) : Prop where
  zero : s.nr 30 = 0
  one : s.nr 31 = 1
  limit : s.nr 57 = A.q
  counts : ∀ r : Fin A.d, s.nr (stateReg r.val) = i r
  values : ∀ r : Fin A.d, i r + 1 < A.q → s.rm (s.nr 49 + s.nr (strideReg r.val)) = 1 - nextValue A T v i r

theorem neighbors_of_cells {k : ℕ} (A : ClockCall k) (T : MultiTable A.d) (base v : ℕ) (i : Fin A.d → ℕ)
    (s : Store) (hz : s.nr 30 = 0) (hone : s.nr 31 = 1) (hq : s.nr 57 = A.q)
    (haddr : s.nr 49 = scanAddress base A.I.graph.n A.q v i)
    (hstate : ∀ r : Fin A.d, s.nr (stateReg r.val) = i r)
    (hstr : ∀ r : Fin A.d, s.nr (strideReg r.val) = stride A.I.graph.n A.q r)
    (hc : ∀ r : Fin A.d, i r + 1 < A.q →
      s.rm (scanAddress base A.I.graph.n A.q v (Function.update i r (i r + 1))) = 1 - nextValue A T v i r) :
    Neighbors A T v i s := by
  refine ⟨hz, hone, hq, hstate, ?_⟩
  intro r hr
  rw [haddr, hstr r, ← scanAddress_tick]
  exact hc r hr

theorem probe_run {k : ℕ} (A : ClockCall k) (T : MultiTable A.d) (v : ℕ) (i : Fin A.d → ℕ)
    (r : Fin A.d) (input : RAMInput) (s : Store) (h : Neighbors A T v i s) :
    ∃ t n, Run input (probe r.val) s t n ∧ t.rr 91 = nextValue A T v i r ∧ n ≤ 7 := by
  let p := (increment r.val).eval input s
  have hp : p = {s with nr := Function.update s.nr 86 (i r + 1)} := by
    simp [p, increment, Atom.eval, ramStep, Store.ofRAM, Store.at, evalNat, h.counts r, h.one]
  have hstride : strideReg r.val ≠ 86 := by have := stride_large r.val; omega
  by_cases hlt : i r + 1 < A.q
  · have hg : (Guard.nat .lt 86 57).eval p = true := by simp [hp, Guard.eval, natTest, h.limit, hlt]
    refine ⟨_, 7, Run.seq (Run.atom (increment r.val) s) (Run.branchTrue hg (run_atoms input (fetchOps r.val) p)), ?_, by decide⟩
    simp [fetchOps, evalAtoms, Atom.eval, Store.ofRAM, Store.at, ramStep, evalReal, evalNat, hp, hstride, h.values r hlt]
  · have hg : (Guard.nat .lt 86 57).eval p = false := by simp [hp, Guard.eval, natTest, h.limit, hlt]
    have hsat : ∃ j, A.q ≤ Function.update i r (i r + 1) j := ⟨r, by simpa using not_lt.mp hlt⟩
    refine ⟨_, 3, Run.seq (Run.atom (increment r.val) s) (Run.branchFalse hg (Run.atom saturated p)), ?_, by decide⟩
    simp [saturated, Atom.eval, Store.ofRAM, Store.at, ramStep, nextValue, value, hsat]

theorem neighbors_frame {k : ℕ} {A : ClockCall k} {T : MultiTable A.d} {v : ℕ} {i : Fin A.d → ℕ} {s t : Store}
    (h : Neighbors A T v i s) (hn : ∀ a, a < 86 ∨ 90 < a → t.nr a = s.nr a) (hr : t.rm = s.rm) :
    Neighbors A T v i t := by
  refine ⟨(hn _ (by omega)).trans h.zero, (hn _ (by omega)).trans h.one, (hn _ (by omega)).trans h.limit,
    fun r => (hn _ (by have := state_large r.val; omega)).trans (h.counts r), ?_⟩
  intro r hh
  rw [hr, hn 49 (by omega), hn _ (by have := stride_large r.val; omega)]
  exact h.values r hh

theorem neighbors_step {k : ℕ} {A : ClockCall k} {T : MultiTable A.d} {v : ℕ} {i : Fin A.d → ℕ}
    {input : RAMInput} {r n : ℕ} {s t : Store} (h : Neighbors A T v i s) (he : Run input (step r) s t n) :
    Neighbors A T v i t := by
  apply neighbors_frame h _ (he.realMemory_frame rfl)
  intro a ha
  apply he.nat_frame
  simp [step, probe, increment, fetchOps, saturated, choose, saveOps, Cmd.atoms, Cmd.natWrites, Atom.natWrites]
  omega

end NearLinearRSP.TwoResources.Supplement.LayerRAM

end

section

set_option autoImplicit false
set_option maxHeartbeats 1500000

namespace NearLinearRSP.TwoResources.Supplement.LayerRAM
open Mission.Structured

def Winner {d : ℕ} (f : Fin d → ℝ) : Option (Fin d) → Store → Prop
  | none, s => s.nr 89 = 0
  | some r, s => s.nr 89 = 1 ∧ s.nr 90 = r.val ∧ s.rr 90 = f r

theorem winner_save {d : ℕ} (f : Fin d → ℝ) (r : Fin d) (input : RAMInput) (s : Store)
    (hc : s.rr 91 = f r) : Winner f (some r) (evalAtoms input (saveOps r.val) s) := by
  simp [Winner, saveOps, evalAtoms, Atom.eval, Store.ofRAM, Store.at, ramStep, hc]

theorem choose_run {d : ℕ} (f : Fin d → ℝ) (r : Fin d) (b : Option (Fin d))
    (input : RAMInput) (s : Store) (hb : Winner f b s) (hz : s.nr 30 = 0) (hc : s.rr 91 = f r) :
    ∃ t n, Run input (choose r.val) s t n ∧ Winner f (keepCandidate f b r) t ∧ n ≤ 6 := by
  have hsave := run_atoms input (saveOps r.val) s
  have hw := winner_save f r input s hc
  cases b with
  | none =>
    change s.nr 89 = 0 at hb
    exact ⟨_, 5, Run.branchTrue (by simp [Guard.eval, natTest, hb, hz]) hsave, hw, by decide⟩
  | some a =>
    obtain ⟨h1, hi, hv⟩ := hb
    have hflag : (Guard.nat .eq 89 30).eval s = false := by simp [Guard.eval, natTest, h1, hz]
    by_cases hlt : f r < f a
    · exact ⟨_, 6, Run.branchFalse hflag (Run.branchTrue (by simp [Guard.eval, realTest, hc, hv, hlt]) hsave),
        by simpa [keepCandidate, hlt] using hw, by decide⟩
    · exact ⟨s, 2, Run.branchFalse hflag (Run.branchFalse (by simp [Guard.eval, realTest, hc, hv, hlt]) (Run.skip s)),
        by simpa [keepCandidate, hlt, Winner] using And.intro h1 (And.intro hi hv), by decide⟩

theorem step_run {k : ℕ} (A : ClockCall k) (T : MultiTable A.d) (v : ℕ) (i : Fin A.d → ℕ)
    (r : Fin A.d) (b : Option (Fin A.d)) (input : RAMInput) (s : Store) (h : Neighbors A T v i s)
    (hb : Winner (nextValue A T v i) b s) :
    ∃ t n, Run input (step r.val) s t n ∧ Neighbors A T v i t ∧
      Winner (nextValue A T v i) (keepCandidate (nextValue A T v i) b r) t ∧ n ≤ 13 := by
  obtain ⟨p, c, hp, hval, hc⟩ := probe_run A T v i r input s h
  have h0 : p.nr 30 = 0 := (hp.nat_frame 30 (by change 30 ∉ (probe 0).natWrites; decide)).trans h.zero
  have h89 := hp.nat_frame 89 (by change 89 ∉ (probe 0).natWrites; decide)
  have h90 := hp.nat_frame 90 (by change 90 ∉ (probe 0).natWrites; decide)
  have h90r := hp.real_frame 90 (by change 90 ∉ (probe 0).realWrites; decide)
  have hb' : Winner (nextValue A T v i) b p := by cases b <;> simpa [Winner, h89, h90, h90r] using hb
  obtain ⟨t, n, ht, hwin, hn⟩ := choose_run (nextValue A T v i) r b input p hb' h0 hval
  have he : Run input (step r.val) s t (c + n) := Run.seq hp ht
  exact ⟨t, _, he, neighbors_step h he, hwin, by omega⟩

theorem scan_run {k : ℕ} (A : ClockCall k) (T : MultiTable A.d) (v : ℕ) (i : Fin A.d → ℕ)
    (rs : List (Fin A.d)) (b : Option (Fin A.d)) (input : RAMInput) (s : Store) (h : Neighbors A T v i s)
    (hb : Winner (nextValue A T v i) b s) :
    ∃ t n, Run input (scan (rs.map Fin.val)) s t n ∧
      Winner (nextValue A T v i) (rs.foldl (keepCandidate (nextValue A T v i)) b) t ∧ n ≤ 13 * rs.length := by
  induction rs generalizing b s with
  | nil => exact ⟨s, 0, Run.skip s, hb, by simp⟩
  | cons r rs ih =>
    obtain ⟨p, c, hp, hnew, hw, hc⟩ := step_run A T v i r b input s h hb
    obtain ⟨t, m, ht, hf, hm⟩ := ih _ p hnew hw
    exact ⟨t, c + m, Run.seq hp ht, hf, by simp only [List.length_cons]; omega⟩

theorem seed_run {k : ℕ} (A : ClockCall k) (T : MultiTable A.d) (v : ℕ) (i : Fin A.d → ℕ) (hd : 0 < A.d)
    (input : RAMInput) (s : Store) (h : Neighbors A T v i s) (hv : s.nr 76 = v) (hs : s.nr 5 = A.I.source) :
    ∃ t n, Run input (seedCmd A.d) s t n ∧ t.rr 90 = (initializeLayer A T i).keys v ∧
      t.nr 89 = multiParentTag ((initializeLayer A T i).parents v) ∧
      t.nr 90 = multiParentPayload ((initializeLayer A T i).parents v) ∧ n ≤ 13 * A.d + 5 := by
  by_cases hsrc : v = A.I.source
  · have hg : (Guard.nat .eq 76 5).eval s = true := by simp [Guard.eval, natTest, hv, hs, hsrc]
    refine ⟨_, 5, Run.branchTrue hg (run_atoms input sourceOps s), ?_, ?_, ?_, by omega⟩
    all_goals simp [sourceOps, evalAtoms, Atom.eval, Store.ofRAM, Store.at, ramStep, initializeLayer, hsrc, multiParentTag, multiParentPayload]
  · let p := beginScan.eval input s
    have hN : Neighbors A T v i p := neighbors_frame h (fun a hh => by
      simp [p, beginScan, Atom.eval, Store.ofRAM, Store.at, ramStep, Function.update_of_ne (show a ≠ 89 by omega)]) rfl
    have hnil : Winner (nextValue A T v i) none p := rfl
    obtain ⟨t, c, he, hwin, hc⟩ := scan_run A T v i (List.finRange A.d) none input p hN hnil
    have hmap : (List.finRange A.d).map Fin.val = List.range A.d := by ext j <;> simp
    rw [hmap] at he
    have hlens : (List.finRange A.d).length = A.d := by simp
    rw [hlens] at hc
    cases hlist : List.finRange A.d with
    | nil => rw [hlist] at hlens; simp at hlens; omega
    | cons r rs =>
      let f := nextValue A T v i
      let w := selectMin f (r :: rs) r
      have hnt : nextTick A T v i = some w := by unfold nextTick; rw [hlist]; rfl
      rw [hlist, candidate_choice] at hwin
      obtain ⟨hflag, hidx, hval⟩ := hwin
      have hg : (Guard.nat .eq 76 5).eval s = false := by simp [Guard.eval, natTest, hv, hs, hsrc]
      refine ⟨t, 1 + (1 + c), Run.branchFalse hg (Run.seq (Run.atom beginScan s) he), ?_, ?_, ?_, by omega⟩
      · simpa [initializeLayer, hsrc, hnt, w, f, nextValue] using hval
      · simpa [initializeLayer, hsrc, hnt, multiParentTag] using hflag
      · simpa [initializeLayer, hsrc, hnt, multiParentPayload, w, f] using hidx

end NearLinearRSP.TwoResources.Supplement.LayerRAM

end

section

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace NearLinearRSP.TwoResources.Supplement.LayerRAM
open Mission.Structured TableQuery

theorem scan_registers (xs : List ℕ) (a : ℕ) (ha : a < 86 ∨ 90 < a) : a ∉ (scan xs).natWrites := by
  induction xs with
  | nil => simp [scan, Cmd.natWrites]
  | cons r rs ih =>
    have hs : a ∉ (step r).natWrites := by
      simp [step, probe, increment, fetchOps, saturated, choose, saveOps, Cmd.atoms, Cmd.natWrites, Atom.natWrites]
      omega
    simp [scan, Cmd.natWrites, hs, ih]

theorem scan_memory (xs : List ℕ) : (scan xs).writesNatMemory = false ∧ (scan xs).writesRealMemory = false := by
  induction xs with
  | nil => exact ⟨rfl, rfl⟩
  | cons r rs ih =>
    change (false || (scan rs).writesNatMemory) = false ∧ (false || (scan rs).writesRealMemory) = false
    simpa using ih

theorem seed_frame {input : RAMInput} {d n : ℕ} {s t : Store} (hr : Run input (seedCmd d) s t n) :
    (∀ a, a < 86 ∨ 90 < a → t.nr a = s.nr a) ∧ t.nm = s.nm ∧ t.rm = s.rm := by
  refine ⟨?_, hr.natMemory_frame ?_, hr.realMemory_frame ?_⟩
  · intro a ha
    apply hr.nat_frame
    simp [seedCmd, sourceOps, beginScan, Cmd.atoms, Cmd.natWrites, Atom.natWrites, scan_registers _ a ha]
    omega
  · exact (scan_memory (List.range d)).1
  · exact (scan_memory (List.range d)).2

noncomputable def atVertex (d : ℕ) (input : RAMInput) (s : Store) := added 49 76 (d + 4) (evalAtoms input vertexOps s)

theorem vertex_run (d : ℕ) (input : RAMInput) (s : Store) :
    let t := atVertex d input s
    Run input (vertexCmd d) s t (d + 7) ∧ t.nr 76 = s.nm (s.nr 142 + s.nr 93) ∧
      t.nr 49 = s.nr 98 + (d + 4) * s.nm (s.nr 142 + s.nr 93) ∧
      (∀ j, j ≠ 49 → j ≠ 76 → t.nr j = s.nr j) ∧ t.nm = s.nm ∧ t.rm = s.rm := by
  have he := Run.seq (run_atoms input vertexOps s) (add_copies_run input 49 76 (by decide) (d + 4) _)
  have hc : vertexOps.length + (d + 4) = d + 7 := by change 3 + (d + 4) = _; omega
  refine ⟨hc ▸ he, ?_⟩
  simp +contextual [atVertex, added, vertexOps, evalAtoms, Atom.eval, Store.ofRAM, Store.at, ramStep, evalNat]

theorem seed_vertex_run {k : ℕ} (A : ClockCall k) (T : MultiTable A.d) (base v : ℕ) (i : Fin A.d → ℕ)
    (input : RAMInput) (s : Store) (hd : 0 < A.d) (hz : s.nr 30 = 0) (hone : s.nr 31 = 1)
    (hq : s.nr 57 = A.q) (hs : s.nr 5 = A.I.source) (hrow : s.nr 98 = scanAddress base A.I.graph.n A.q 0 i)
    (hv : s.nm (s.nr 142 + s.nr 93) = v) (hstate : ∀ r : Fin A.d, s.nr (stateReg r.val) = i r)
    (hstr : ∀ r : Fin A.d, s.nr (strideReg r.val) = stride A.I.graph.n A.q r)
    (hc : ∀ r : Fin A.d, i r + 1 < A.q → s.rm (scanAddress base A.I.graph.n A.q v
        (Function.update i r (i r + 1))) = 1 - nextValue A T v i r) :
    let a := scanAddress base A.I.graph.n A.q v i
    let init := initializeLayer A T i
    ∃ t n, Run input (seedVertex A.d) s t n ∧ t.nr 93 = s.nr 93 + 1 ∧
      t.nm = Function.update (Function.update s.nm a (multiParentTag (init.parents v))) (a + 1) (multiParentPayload (init.parents v)) ∧
      t.rm = Function.update s.rm (s.nr 189 + s.nr 93) (init.keys v) ∧
      (∀ j, j ≠ 49 → j ≠ 76 → j ≠ 93 → (j < 86 ∨ 90 < j) → t.nr j = s.nr j) ∧ n ≤ 14 * A.d + 18 := by
  let p := atVertex A.d input s
  obtain ⟨hp, hpv, hpa, hpr, hpn, hpm⟩ := vertex_run A.d input s
  have vreg : p.nr 76 = v := hpv.trans hv
  have addr : p.nr 49 = scanAddress base A.I.graph.n A.q v i := by
    rw [hpa, hv, hrow]; unfold scanAddress; ring
  have high (a : ℕ) (ha : 100 ≤ a) := hpr a (by omega) (by omega)
  have hnb := neighbors_of_cells A T base v i p ((hpr 30 (by decide) (by decide)).trans hz)
    ((hpr 31 (by decide) (by decide)).trans hone) ((hpr 57 (by decide) (by decide)).trans hq) addr
    (fun r => (high _ (state_large r.val)).trans (hstate r)) (fun r => (high _ (stride_large r.val)).trans (hstr r))
    (fun r hlt => by rw [hpm]; exact hc r hlt)
  obtain ⟨u, c, hu, hkey, htag, hpay, hcost⟩ := seed_run A T v i hd input p hnb vreg ((hpr 5 (by decide) (by decide)).trans hs)
  obtain ⟨hureg, hun, hum⟩ := seed_frame hu
  have same (j : ℕ) (h49 : j ≠ 49) (h76 : j ≠ 76) (hj : j < 86 ∨ 90 < j) :=
    (hureg j hj).trans (hpr j h49 h76)
  have u49 := (hureg 49 (by omega)).trans addr
  have u31 := (same 31 (by decide) (by decide) (by omega)).trans hone
  have u93 := same 93 (by decide) (by decide) (by omega)
  have u189 := same 189 (by decide) (by decide) (by omega)
  refine ⟨_, (A.d + 7) + (c + 6), Run.seq hp (Run.seq hu (run_atoms input commitSeed u)), ?_, ?_, ?_, ?_, by omega⟩
  · simp [commitSeed, evalAtoms, Atom.eval, Store.ofRAM, Store.at, ramStep, evalNat, u93, u31]
  · simp [commitSeed, evalAtoms, Atom.eval, Store.ofRAM, Store.at, ramStep, evalNat, u49, u31, hun.trans hpn, htag, hpay]
  · simp [commitSeed, evalAtoms, Atom.eval, Store.ofRAM, Store.at, ramStep, evalNat, u189, u93, hum.trans hpm, hkey]
  · intro j h49 h76 h93 hj
    simpa [commitSeed, evalAtoms, Atom.eval, Store.ofRAM, Store.at, ramStep, Function.update_of_ne h93,
      Function.update_of_ne (show j ≠ 86 by omega)] using same j h49 h76 hj

end NearLinearRSP.TwoResources.Supplement.LayerRAM

end

section

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace NearLinearRSP.TwoResources.Supplement.LayerRAM
open Mission.Structured TableQuery
open Mission.Queue (slotVertex)

noncomputable def vertexAt {k : ℕ} (A : ClockCall k) (j : ℕ) := slotVertex (incidentVertices A.I) j

theorem vertexAt_mem {k : ℕ} (A : ClockCall k) (j : ℕ) (hj : j < (incidentVertices A.I).length) :
    vertexAt A j ∈ incidentVertices A.I := by
  simp [vertexAt, slotVertex, List.getElem?_eq_getElem hj]

theorem row_ascending {k : ℕ} (A : ClockCall k) (base : ℕ) (i : Fin A.d → ℕ) (u v : ℕ) (hu : u < v) :
    rowCell A base i u + (A.d + 4) ≤ rowCell A base i v := by
  have h := Nat.mul_le_mul_left (A.d + 4) (Nat.succ_le_of_lt hu)
  rw [Nat.mul_succ] at h
  simp only [rowCell, scanAddress, Nat.mul_add]
  omega

theorem row_disjoint {k : ℕ} (A : ClockCall k) (base : ℕ) (i : Fin A.d → ℕ) (u v x y : ℕ)
    (hne : u ≠ v) (hx : x < A.d + 4) (hy : y < A.d + 4) :
    rowCell A base i u + x ≠ rowCell A base i v + y := by
  rcases Nat.lt_or_gt_of_ne hne with h | h
  · have := row_ascending A base i u v h; omega
  · have := row_ascending A base i v u h; omega

structure Row {k : ℕ} (A : ClockCall k) (T : MultiTable A.d) (base array keys : ℕ)
    (i : Fin A.d → ℕ) (s : Store) : Prop where
  zero : s.nr 30 = 0
  one : s.nr 31 = 1
  q : s.nr 57 = A.q
  source : s.nr 5 = A.I.source
  start : s.nr 98 = rowCell A base i 0
  arrayReg : s.nr 142 = array
  number : s.nr 143 = (incidentVertices A.I).length
  keysReg : s.nr 189 = keys
  counts : ∀ r : Fin A.d, s.nr (stateReg r.val) = i r
  strides : ∀ r : Fin A.d, s.nr (strideReg r.val) = stride A.I.graph.n A.q r
  vertices : ∀ j < (incidentVertices A.I).length, s.nm (array + j) = vertexAt A j
  next : ∀ v ∈ incidentVertices A.I, ∀ r : Fin A.d, i r + 1 < A.q →
    s.rm (rowCell A base (Function.update i r (i r + 1)) v) = 1 - nextValue A T v i r

def Seeded {k : ℕ} (A : ClockCall k) (T : MultiTable A.d) (base keys : ℕ) (i : Fin A.d → ℕ) (j : ℕ) (s : Store) : Prop :=
  ∀ l < j, let v := vertexAt A l
    let a := rowCell A base i v
    let init := initializeLayer A T i
    s.nm a = multiParentTag (init.parents v) ∧ s.nm (a + 1) = multiParentPayload (init.parents v) ∧ s.rm (keys + l) = init.keys v

def SeedFrame {k : ℕ} (A : ClockCall k) (base keys : ℕ) (i : Fin A.d → ℕ) (s t : Store) : Prop :=
  (∀ a, (∀ v ∈ incidentVertices A.I, a ≠ rowCell A base i v ∧ a ≠ rowCell A base i v + 1) → t.nm a = s.nm a) ∧
  (∀ a, a < keys ∨ keys + (incidentVertices A.I).length ≤ a → t.rm a = s.rm a)

theorem seed_advance {k : ℕ} (A : ClockCall k) (T : MultiTable A.d) (base array keys : ℕ) (i : Fin A.d → ℕ)
    (input : RAMInput) (hd : 0 < A.d) (hi : ∀ r, i r < A.q) (ha : extent A base ≤ array)
    (hk : extent A base ≤ keys) (initial s : Store) (j : ℕ) (hj : j < (incidentVertices A.I).length)
    (h : Row A T base array keys i s) (hc : s.nr 93 = j) (hseed : Seeded A T base keys i j s)
    (hframe : SeedFrame A base keys i initial s) :
    ∃ t n, Run input (seedVertex A.d) s t n ∧ Row A T base array keys i t ∧ t.nr 93 = j + 1 ∧
      Seeded A T base keys i (j + 1) t ∧ SeedFrame A base keys i initial t ∧ n ≤ 14 * A.d + 18 := by
  let v := vertexAt A j
  let w := rowCell A base i v
  let U := initializeLayer A T i
  have hvm : v ∈ incidentVertices A.I := vertexAt_mem A j hj
  have hv : v < A.I.graph.n := incident_valid A.I v hvm
  obtain ⟨t, n, he, htj, hnmem, hrmem, hregs, hn⟩ := seed_vertex_run A T base v i input s hd h.zero h.one h.q h.source h.start
    (by rw [h.arrayReg, hc]; exact h.vertices j hj) h.counts h.strides (h.next v hvm)
  change t.nm = Function.update (Function.update s.nm w (multiParentTag (U.parents v))) (w + 1) (multiParentPayload (U.parents v)) at hnmem
  change t.rm = Function.update s.rm (s.nr 189 + s.nr 93) (U.keys v) at hrmem
  rw [h.keysReg, hc] at hrmem
  have reg (a : ℕ) (h1 : a ≠ 49) (h2 : a ≠ 76) (h3 : a ≠ 93) (h4 : a < 86 ∨ 90 < a) := hregs a h1 h2 h3 h4
  have high (a : ℕ) (ha : 100 ≤ a) := reg a (by omega) (by omega) (by omega) (by omega)
  have cellEnd : w + 1 < extent A base := scanAddress_inside A base v hv i hi 1 (by omega)
  have natKeep (a : ℕ) (h1 : a ≠ w) (h2 : a ≠ w + 1) : t.nm a = s.nm a := by
    simp only [hnmem, Function.update_of_ne h1, Function.update_of_ne h2]
  have realKeep (a : ℕ) (h1 : a ≠ keys + j) : t.rm a = s.rm a := by simp only [hrmem, Function.update_of_ne h1]
  refine ⟨t, n, he, ?_, htj.trans (by rw [hc]), ?_, ?_, hn⟩
  · refine ⟨(reg 30 (by decide) (by decide) (by decide) (by decide)).trans h.zero,
      (reg 31 (by decide) (by decide) (by decide) (by decide)).trans h.one,
      (reg 57 (by decide) (by decide) (by decide) (by decide)).trans h.q,
      (reg 5 (by decide) (by decide) (by decide) (by decide)).trans h.source,
      (reg 98 (by decide) (by decide) (by decide) (by decide)).trans h.start,
      (high 142 (by decide)).trans h.arrayReg, (high 143 (by decide)).trans h.number,
      (high 189 (by decide)).trans h.keysReg, fun r => (high _ (state_large r.val)).trans (h.counts r),
      fun r => (high _ (stride_large r.val)).trans (h.strides r), ?_, ?_⟩
    · intro l hl
      exact (natKeep _ (by omega) (by omega)).trans (h.vertices l hl)
    · intro x hx r hr
      have hi' (b : Fin A.d) : Function.update i r (i r + 1) b < A.q := by
        by_cases hb : b = r <;> simp [Function.update_apply, hb, hi, hr]
      have hupper := scanAddress_inside A base x (incident_valid A.I x hx) _ hi' 0 (by omega)
      change rowCell A base (Function.update i r (i r + 1)) x + 0 < extent A base at hupper
      exact (realKeep _ (by omega)).trans (h.next x hx r hr)
  · intro l hl
    by_cases hlj : l = j
    · subst l
      change t.nm w = _ ∧ t.nm (w + 1) = _ ∧ t.rm (keys + j) = _
      simp [hnmem, hrmem, v, U]
    · have hl' : l < j := by omega
      obtain ⟨htag, hparent, hkey⟩ := hseed l hl'
      have hvne : vertexAt A l ≠ v := fun hh =>
        hlj ((Mission.Queue.slotVertex_injective _ (incident_nodup A.I) l j (by omega) hj).mp hh)
      have sep (x y : ℕ) (hx : x < A.d + 4) (hy : y < A.d + 4) :
          rowCell A base i (vertexAt A l) + x ≠ w + y := row_disjoint A base i _ v x y hvne hx hy
      refine ⟨(natKeep _ (by simpa using sep 0 0 (by omega) (by omega)) (by simpa using sep 0 1 (by omega) (by omega))).trans htag,
        (natKeep _ (by simpa using sep 1 0 (by omega) (by omega)) (sep 1 1 (by omega) (by omega))).trans hparent,
        (realKeep _ (by omega)).trans hkey⟩
  · exact ⟨fun a hside => (natKeep _ (hside v hvm).1 (hside v hvm).2).trans (hframe.1 a hside),
      fun a hside => (realKeep _ (by omega)).trans (hframe.2 a hside)⟩

end NearLinearRSP.TwoResources.Supplement.LayerRAM

end

section

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace NearLinearRSP.TwoResources.Supplement.LayerRAM
open Mission.Structured
open Mission.Queue (Record activeLeaf vertexRecord readRecord Represents WinnerFrame)

structure Heap (B W P : ℕ) (leaf : ℕ → Record) (s : Store) : Prop where
  disjoint : W + 2 * B ≤ P
  records : Represents B W leaf s
  parents : ∀ j < 2 * B, s.nm (P + j) = j / 2

theorem Heap.congr {B W P : ℕ} {leaf : ℕ → Record} {s t : Store} (h : Heap B W P leaf s)
    (ht : ∀ j < 2 * B, t.nm (W + j) = s.nm (W + j) ∧ t.rm (W + j) = s.rm (W + j))
    (hp : ∀ j < 2 * B, t.nm (P + j) = s.nm (P + j)) : Heap B W P leaf t := by
  refine ⟨h.disjoint, ?_, fun j hj => (hp j hj).trans (h.parents j hj)⟩
  intro j hj
  calc
    _ = readRecord s (W + j) := by simp [readRecord, (ht j hj).1, (ht j hj).2]
    _ = _ := h.records j hj

theorem heap_root (xs q : List ℕ) (key : ℕ → ℝ) (height W P first : ℕ) (s : Store)
    (hxs : xs.Nodup) (hq : q.Sublist xs) (hB : xs.length ≤ 2 ^ height) (hne : q ≠ [])
    (h : Heap (2 ^ height) W P (activeLeaf xs q key (2 ^ height)) s) :
    let u := selectMin key q first
    s.nm (W + 1) = xs.idxOf u + 1 ∧ s.rm (W + 1) = key u := by
  have hroot := h.records 1 (show 1 < 2 * 2 ^ height by have := Nat.one_le_two_pow (n := height); omega)
  have hw := Mission.Queue.activeLeaf_firstMin xs q key height hxs hq hB first hne
  rw [← hroot] at hw
  unfold Mission.Queue.Record.decode at hw
  split at hw
  · contradiction
  · have he := Option.some.inj hw
    exact ⟨congrArg Record.token he, congrArg Record.key he⟩

theorem heap_leaf (xs q : List ℕ) (key : ℕ → ℝ) (B W P v : ℕ) (s : Store)
    (hB : xs.length ≤ B) (hv : v ∈ xs) (h : Heap B W P (activeLeaf xs q key B) s) :
    let j := xs.idxOf v
    s.nm (W + (B + j)) = (if v ∈ q then j + 1 else 0) ∧ s.rm (W + (B + j)) = key v := by
  have hj : xs.idxOf v < xs.length := List.idxOf_lt_length_of_mem hv
  have he := h.records (B + xs.idxOf v) (by omega)
  rw [Mission.Queue.heapTruth_leaf _ _ _ (by omega), Mission.Queue.activeLeaf_at _ _ _ _ _ hj,
    Mission.Queue.slotVertex_idxOf_eq xs v hv] at he
  exact ⟨congrArg Record.token he, congrArg Record.key he⟩

theorem write_leaf (input : RAMInput) (B W P : ℕ) (leaf : ℕ → Record) (s : Store)
    (h : Heap B W P leaf s) (cfg : Config B W P s) (hj : s.nr 95 < B) :
    ∃ t n, Run input updateCmd s t n ∧
      Heap B W P (Function.update leaf (B + s.nr 95) ⟨s.nr 96, s.rr 94⟩) t ∧
      WinnerFrame W (2 * B) s t ∧ n ≤ 19 * Nat.clog 2 (2 * B) + 13 := by
  let p := evalAtoms input updateOps s
  have hp : p.nr 0 = B + s.nr 95 ∧ p.nr 1 = W ∧ p.nr 2 = P ∧ p.nr 3 = 0 ∧ p.nr 4 = 1 ∧
      p.nr 10 = s.nr 96 ∧ p.rr 2 = s.rr 94 := by
    simp [p, updateOps, evalAtoms, Atom.eval, Store.ofRAM, Store.at, ramStep, evalNat,
      cfg.capacity, cfg.winnerBase, cfg.parentBase]
  obtain ⟨h0, h1, h2, h3, h4, h10, hr⟩ := hp
  have hl : Mission.Queue.ParentLayout (2 * B) p := by
    refine ⟨by omega, by rw [h1, h2]; exact h.disjoint, h3, ?_⟩
    intro j hh; rw [h2]; exact h.parents j hh
  have hrep : Represents B (p.nr 1) leaf p := by rw [h1]; exact h.records
  obtain ⟨t, c, he, hc, _, hkeep, hpl, hnew, hframe⟩ := Mission.Queue.updateLeaf_refines input B leaf p hl h4
    (by omega) (by omega) hrep
  have hp2 : t.nr 2 = P := (hkeep 2 (by decide) (by decide)).trans h2
  rw [h1, h0, h10, hr] at hnew
  rw [h1] at hframe
  refine ⟨t, 7 + c, Run.seq (run_atoms input updateOps s) he, ⟨h.disjoint, hnew, ?_⟩, hframe, by omega⟩
  intro j hh
  simpa only [hp2] using hpl.2.2.2 j hh

theorem decrease_heap (xs q : List ℕ) (key : ℕ → ℝ) (v : ℕ) (score : ℝ) (B W P : ℕ) (input : RAMInput) (s : Store)
    (hx : xs.Nodup) (hv : v ∈ xs) (hq : v ∈ q) (hB : xs.length ≤ B)
    (cfg : Config B W P s) (h : Heap B W P (activeLeaf xs q key B) s)
    (hi : s.nr 95 = xs.idxOf v) (ht : s.nr 96 = xs.idxOf v + 1) (hs : s.rr 94 = score) :
    ∃ t n, Run input updateCmd s t n ∧ Heap B W P (activeLeaf xs q (Function.update key v score) B) t ∧
      WinnerFrame W (2 * B) s t ∧ n ≤ 19 * Nat.clog 2 (2 * B) + 13 := by
  have hj := List.idxOf_lt_length_of_mem hv
  obtain ⟨t, n, he, hp, hf, hc⟩ := write_leaf input B W P _ s h cfg (by omega)
  rw [Mission.Queue.activeLeaf_update_vertex xs q key B v score hx hv hq]
  exact ⟨t, n, he, by simpa only [hi, ht, hs] using hp, hf, hc⟩

end NearLinearRSP.TwoResources.Supplement.LayerRAM

end

section

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace NearLinearRSP.TwoResources.Supplement.LayerRAM
open Mission.Structured
open Mission.Queue (activeLeaf slotVertex WinnerFrame InitFrame)

theorem build_heap (xs : List ℕ) (key : ℕ → ℝ) (B W P R : ℕ) (input : RAMInput) (s : Store)
    (cfg : Config B W P s) (hN : s.nr 143 = xs.length) (hR : s.nr 189 = R)
    (hpos : 0 < B) (hB : xs.length ≤ B) (hspace : W + 2 * B ≤ P) (hdis : R + xs.length ≤ W)
    (hkey : ∀ i < xs.length, s.rm (R + i) = key (slotVertex xs i)) :
    ∃ t n, Run input buildHeap s t n ∧ Heap B W P (activeLeaf xs xs key B) t ∧
      InitFrame W P B s t ∧ n ≤ 15 * B + (19 * Nat.clog 2 (2 * B) + 13) * xs.length + 10 := by
  let p := evalAtoms input buildOps s
  have hfields : p.nr 1 = W ∧ p.nr 2 = P ∧ p.nr 3 = 0 ∧ p.nr 4 = 1 ∧ p.nr 11 = B ∧ p.nr 12 = xs.length ∧ p.nr 13 = R := by
    simp [p, buildOps, evalAtoms, Atom.eval, Store.ofRAM, Store.at, ramStep, cfg.capacity, cfg.winnerBase, cfg.parentBase, hN, hR]
  obtain ⟨h1, h2, h3, h4, h11, h12, h13⟩ := hfields
  obtain ⟨t, c, hr, hi, hc⟩ := Mission.Queue.buildQueue_run input B xs.length W P R p hpos hB hspace
    (fun i hh => Or.inl (by omega)) h1 h2 h3 h4 h11 h12 h13
  have hleaf : activeLeaf xs xs key B = Mission.Queue.prefixLeaf B (fun i => p.rm (R + i)) xs.length := by
    rw [Mission.Queue.activeLeaf_initial]
    funext node
    unfold Mission.Queue.prefixLeaf
    split_ifs with hn
    · exact congrArg (fun x => (⟨node - B + 1, x⟩ : Mission.Queue.Record)) (hkey (node - B) (by omega)).symm
    · rfl
  refine ⟨t, 7 + c, Run.seq (run_atoms input buildOps s) hr, ⟨hspace, hleaf ▸ hi.represents, ?_⟩, hi.frame, by omega⟩
  intro j hj
  simpa only [hi.hP] using hi.parents.2.2.2 j hj

theorem pop_heap (xs q : List ℕ) (key : ℕ → ℝ) (height W P fallback : ℕ) (input : RAMInput) (s : Store)
    (cfg : Config (2 ^ height) W P s) (h : Heap (2 ^ height) W P (activeLeaf xs q key (2 ^ height)) s)
    (hx : xs.Nodup) (hq : q.Sublist xs) (hB : xs.length ≤ 2 ^ height) (hne : q ≠ [])
    (hvertices : ∀ v ∈ xs, s.nm (s.nr 142 + xs.idxOf v) = v) :
    let u := selectMin key q fallback
    ∃ t n, Run input popCmd s t n ∧ t.nr 97 = u ∧ t.rr 94 = key u ∧
      Heap (2 ^ height) W P (activeLeaf xs (q.erase u) key (2 ^ height)) t ∧
      WinnerFrame W (2 * 2 ^ height) s t ∧ n ≤ 19 * Nat.clog 2 (2 * 2 ^ height) + 21 := by
  let u := selectMin key q fallback
  let p := evalAtoms input rootOps s
  have huq : u ∈ q := firstMin_mem key q fallback hne
  have hu : u ∈ xs := hq.subset huq
  have hidx := List.idxOf_lt_length_of_mem hu
  obtain ⟨ha, hd⟩ := heap_root xs q key height W P fallback s hx hq hB hne h
  change s.nm (W + 1) = xs.idxOf u + 1 at ha
  change s.rm (W + 1) = key u at hd
  have hp : p.nr 95 = xs.idxOf u ∧ p.nr 96 = 0 ∧ p.nr 97 = u ∧ p.rr 94 = key u := by
    simp [p, rootOps, evalAtoms, Atom.eval, Store.ofRAM, Store.at, ramStep, evalNat, cfg.winnerBase, ha, hd, hvertices u hu]
  obtain ⟨hj, ht0, hpu, hpk⟩ := hp
  have hcfg : Config (2 ^ height) W P p := ⟨cfg.winnerBase, cfg.parentBase, cfg.capacity⟩
  have hheap : Heap (2 ^ height) W P (activeLeaf xs q key (2 ^ height)) p :=
    h.congr (fun _ _ => ⟨rfl, rfl⟩) (fun _ _ => rfl)
  obtain ⟨t, c, he, hnew, hfr, hc⟩ := write_leaf input (2 ^ height) W P _ p hheap hcfg (by omega)
  rw [hj, ht0, hpk, ← Mission.Queue.activeLeaf_delete_vertex xs q key _ u hx (hq.nodup hx) hu] at hnew
  exact ⟨t, 8 + c, Run.seq (run_atoms input rootOps s) he, (he.nat_frame 97 (by decide)).trans hpu,
    (he.real_frame 94 (by decide)).trans hpk, hnew, hfr, by omega⟩

end NearLinearRSP.TwoResources.Supplement.LayerRAM

end

section

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace NearLinearRSP.TwoResources.Supplement.SpaceRAM
open Mission.Structured TableQuery

noncomputable def shaped (k d : ℕ) (input : RAMInput) (s : Store) : Store :=
  added 49 60 8 (added 58 60 (d + 4) (evalAtoms input (shapeOps k) s))

theorem shape_run (k d : ℕ) (input : RAMInput) (s : Store) :
    let t := shaped k d input s
    Run input (shapeCmd k d) s t (d + 19) ∧ t.nr 58 = (d + 4) * s.nm 2 ∧ t.nr 57 = s.nm 0 ∧
      t.nr 49 = 32 + 2 * k + 8 * s.nm 2 ∧ t.nr 31 = 1 ∧ t.nm = s.nm ∧ t.rm = s.rm := by
  have he := Run.seq (run_atoms input (shapeOps k) s) (Run.seq
    (add_copies_run input 58 60 (by decide) (d + 4) (evalAtoms input (shapeOps k) s))
    (add_copies_run input 49 60 (by decide) 8 _))
  have hlen : (shapeOps k).length + ((d + 4) + 8) = d + 19 := by change 7 + ((d + 4) + 8) = _; omega
  refine ⟨hlen ▸ he, ?_⟩
  simp [shaped, added, shapeOps, evalAtoms, Atom.eval, Store.ofRAM, Store.at, ramStep]

end NearLinearRSP.TwoResources.Supplement.SpaceRAM

end

section

set_option autoImplicit false
set_option maxHeartbeats 1200000

namespace NearLinearRSP.TwoResources.Supplement.InputValues

def row (k i : ℕ) := k + k * i

theorem row_coordinate {k : ℕ} (I : MultiInstance k) (ε : ℝ) (i : ℕ) (e : ℕ × ℕ)
    (he : I.graph.edges[i]? = some e) (j : Fin k) :
    (multiInput I ε).reals (row k i + j.val) = coordinateWeight I j e.1 e.2 := by
  have hk : 0 < k := Nat.zero_lt_of_lt j.isLt
  have h1 : row k i + j.val ≠ 0 := by unfold row; omega
  have h2 : ¬ row k i + j.val < k := by unfold row; omega
  have hsub : row k i + j.val - k = j.val + k * i := by unfold row; omega
  have hd : (j.val + k * i) / k = i := by simp [Nat.add_mul_div_left, hk, Nat.div_eq_of_lt j.isLt]
  have hm : (j.val + k * i) % k = j.val := by simp [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt j.isLt]
  simp only [multiInput, h1, ↓reduceDIte, h2, hsub, hd, he, hm, j.isLt]

theorem row_length {k : ℕ} (I : MultiInstance k) (hk : 0 < k) (ε : ℝ) (i : ℕ) (e : ℕ × ℕ)
    (he : I.graph.edges[i]? = some e) : (multiInput I ε).reals (row k i) = I.length e.1 e.2 := by
  simpa only [Nat.add_zero, coordinateWeight, ↓reduceDIte] using row_coordinate I ε i e he ⟨0, hk⟩

theorem row_cost {k : ℕ} (I : MultiInstance k) (ε : ℝ) (i : ℕ) (e : ℕ × ℕ)
    (he : I.graph.edges[i]? = some e) (r : Fin (k - 1)) :
    (multiInput I ε).reals (row k i + (r.val + 1)) = I.cost r e.1 e.2 := by
  have h : r.val + 1 < k := by omega
  simpa [coordinateWeight] using row_coordinate I ε i e he ⟨r.val + 1, h⟩

theorem budget_read {k : ℕ} (I : MultiInstance k) (ε : ℝ) (r : Fin (k - 1)) :
    (multiInput I ε).reals (r.val + 1) = I.budget r := by
  have h : r.val + 1 < k := by omega
  simp [multiInput, h]

theorem edge_endpoints {k : ℕ} (I : MultiInstance k) (ε : ℝ) (i : ℕ) (e : ℕ × ℕ)
    (he : I.graph.edges[i]? = some e) :
    (multiInput I ε).naturals (4 + 2 * i) = e.1 ∧
    (multiInput I ε).naturals (4 + 2 * i + 1) = e.2 := by
  have hs : 4 + 2 * i + 1 - 4 = 2 * i + 1 := by omega
  have ht : 4 + 2 * i - 4 = 2 * i := by omega
  have hd : (2 * i + 1) / 2 = i := by omega
  have hm : (2 * i + 1) % 2 = 1 := by omega
  simp [multiInput, hs, ht, hd, hm, he, show 4 + 2 * i ≠ 1 by omega, show 4 + 2 * i ≠ 2 by omega,
    show 4 + 2 * i ≠ 3 by omega, show 4 + 2 * i + 1 ≠ 2 by omega, show 4 + 2 * i + 1 ≠ 3 by omega]

end NearLinearRSP.TwoResources.Supplement.InputValues

end

section

set_option autoImplicit false
set_option maxHeartbeats 1800000

namespace NearLinearRSP.TwoResources.Supplement.LayerRAM
open Mission.Structured TableQuery
open Mission.Queue (activeLeaf)

theorem copies_preserve (dst src n a : ℕ) (ha : a ≠ dst) : a ∉ (addCopies dst src n).natWrites := by
  induction n with
  | zero => simp [addCopies, Cmd.natWrites]
  | succ n ih => simp [addCopies, Cmd.natWrites, Atom.natWrites, ih, ha]

theorem seed_all_high (d a : ℕ) (ha : 100 ≤ a) : a ∉ (seedAll d).natWrites := by
  have hc := copies_preserve 49 76 (d + 4) a (by omega)
  have hs := scan_registers (List.range d) a (by omega)
  simp [seedAll, seedZero, seedVertex, vertexCmd, vertexOps, seedCmd, sourceOps, beginScan,
    commitSeed, Cmd.atoms, Cmd.natWrites, Atom.natWrites, hc, hs]
  omega

theorem seed_all_run {k : ℕ} (A : ClockCall k) (T : MultiTable A.d) (base array keys : ℕ) (i : Fin A.d → ℕ)
    (input : RAMInput) (hd : 0 < A.d) (hi : ∀ r, i r < A.q) (ha : extent A base ≤ array) (hk : extent A base ≤ keys)
    (s : Store) (h : Row A T base array keys i s) :
    ∃ t n, Run input (seedAll A.d) s t n ∧ Row A T base array keys i t ∧
      Seeded A T base keys i (incidentVertices A.I).length t ∧ SeedFrame A base keys i s t ∧
      n ≤ (14 * A.d + 20) * (incidentVertices A.I).length + 2 := by
  let p := seedZero.eval input s
  have hp : p = {s with nr := Function.update s.nr 93 0} := rfl
  have hn : Row A T base array keys i p := by
    obtain ⟨hz, h1, hq, hsrc, hrow, harr, hnum, hkey, hcounts, hstr, hvs, hT⟩ := h
    refine ⟨hz, h1, hq, hsrc, hrow, harr, hnum, hkey, ?_, ?_, hvs, hT⟩
    · intro r; simpa [hp, Function.update_of_ne (show stateReg r.val ≠ 93 by have := state_large r.val; omega)] using hcounts r
    · intro r; simpa [hp, Function.update_of_ne (show strideReg r.val ≠ 93 by have := stride_large r.val; omega)] using hstr r
  let N := (incidentVertices A.I).length
  let P (j : ℕ) (u : Store) := Row A T base array keys i u ∧ u.nr 93 = j ∧ Seeded A T base keys i j u ∧ SeedFrame A base keys i s u
  have hstart : P 0 p := ⟨hn, rfl, fun l hl => (Nat.not_lt_zero _ hl).elim, ⟨fun _ _ => rfl, fun _ _ => rfl⟩⟩
  obtain ⟨t, c, he, hdone, hcost⟩ := run_bounded_loop input (.nat .lt 93 143) (seedVertex A.d) N (14 * A.d + 18) P
    (fun j u _ hu => by simp [Guard.eval, natTest, hu.2.1, hu.1.number, N])
    (fun j u hj hu => by
      obtain ⟨v, m, hr, hrow, hcount, hseed, hf, hc⟩ := seed_advance A T base array keys i input hd hi ha hk s u j hj
        hu.1 hu.2.1 hu.2.2.1 hu.2.2.2
      exact ⟨v, m, hr, ⟨hrow, hcount, hseed, hf⟩, hc⟩) 0 p (by omega) hstart
  refine ⟨t, 1 + c, Run.seq (Run.atom seedZero s) he, hdone.1, hdone.2.2.1, hdone.2.2.2, ?_⟩
  simp only [Nat.sub_zero, N, show (14 * A.d + 18 + 2) = 14 * A.d + 20 by omega] at hcost
  omega

theorem layer_heap_run {k : ℕ} (A : ClockCall k) (T : MultiTable A.d) (base array keys B W P : ℕ) (i : Fin A.d → ℕ)
    (input : RAMInput) (hd : 0 < A.d) (hi : ∀ r, i r < A.q) (ha : extent A base ≤ array) (hk : extent A base ≤ keys)
    (hpos : 0 < B) (hB : (incidentVertices A.I).length ≤ B) (hspace : W + 2 * B ≤ P)
    (hsep : keys + (incidentVertices A.I).length ≤ W) (s : Store) (h : Row A T base array keys i s) (cfg : Config B W P s) :
    let xs := incidentVertices A.I
    let init := initializeLayer A T i
    ∃ t n, Run input (startLayer A.d) s t n ∧ Heap B W P (activeLeaf xs xs init.keys B) t ∧
      Seeded A T base keys i xs.length t ∧
      (∀ a, a < W → (∀ v ∈ xs, a ≠ rowCell A base i v ∧ a ≠ rowCell A base i v + 1) → t.nm a = s.nm a) ∧
      (∀ a, a < keys → t.rm a = s.rm a) ∧
      n ≤ 15 * B + (14 * A.d + 33 + 19 * Nat.clog 2 (2 * B)) * xs.length + 12 := by
  let xs := incidentVertices A.I
  let U := initializeLayer A T i
  obtain ⟨p, c, hp, hrow, hseed, hframe, hc⟩ := seed_all_run A T base array keys i input hd hi ha hk s h
  have reg (a : ℕ) (ha : 100 ≤ a) := hp.nat_frame a (seed_all_high _ a ha)
  have hpCfg : Config B W P p := ⟨(reg 180 (by decide)).trans cfg.winnerBase,
    (reg 181 (by decide)).trans cfg.parentBase, (reg 188 (by decide)).trans cfg.capacity⟩
  obtain ⟨t, m, he, hheap, hf, hm⟩ := build_heap xs U.keys B W P keys input p hpCfg hrow.number hrow.keysReg hpos hB hspace hsep
    (fun l hl => (hseed l hl).2.2)
  have hnat (a : ℕ) (hlt : a < W) := hf.1 a (Or.inl hlt) (Or.inl (by omega))
  have hreal (a : ℕ) (hlt : a < W) := hf.2 a (Or.inl hlt)
  refine ⟨t, c + m, Run.seq hp he, hheap, ?_, fun a hl hside => (hnat a hl).trans (hframe.1 a hside),
    fun a hl => (hreal a (by omega)).trans (hframe.2 a (Or.inl hl)), ?_⟩
  · intro l hl
    have hv := incident_valid A.I _ (vertexAt_mem A l hl)
    have h2 := scanAddress_inside A base _ hv i hi 1 (by omega)
    change rowCell A base i (vertexAt A l) + 1 < extent A base at h2
    obtain ⟨h0, h1, hr⟩ := hseed l hl
    exact ⟨(hnat _ (by omega)).trans h0, (hnat _ (by omega)).trans h1, (hreal _ (by omega)).trans hr⟩
  · dsimp only [xs] at hm ⊢
    nlinarith only [hc, hm]

end NearLinearRSP.TwoResources.Supplement.LayerRAM

end

section

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace NearLinearRSP.TwoResources.Supplement.LayerRAM
open Mission.Structured TableQuery

theorem settle_run {k : ℕ} (A : ClockCall k) (base : ℕ) (i : Fin A.d → ℕ) (u rank : ℕ) (key : ℝ)
    (input : RAMInput) (s : Store) (hrow : s.nr 98 = rowCell A base i 0) (hu : s.nr 97 = u)
    (hk : s.rr 94 = key) (hr : s.nr 191 = rank) :
    let a := rowCell A base i u
    ∃ t, Run input (settleCmd A.d) s t (A.d + 13) ∧ t.nr 99 = a ∧ t.nr 191 = rank + 1 ∧
      t.nm = Function.update s.nm (a + 2) rank ∧ t.rm = Function.update s.rm a (1 - key) ∧
      (∀ j, j ≠ 99 → j ≠ 191 → j ≠ 86 → t.nr j = s.nr j) ∧ (∀ j, j ≠ 91 → t.rr j = s.rr j) := by
  let p := settledAddress.eval input s
  let w := added 99 97 (A.d + 4) p
  let t := evalAtoms input settleOps w
  have ha : w.nr 99 = rowCell A base i u := by
    simp [w, added, p, settledAddress, Atom.eval, Store.ofRAM, Store.at, ramStep, hrow, hu, rowCell, scanAddress]
    ring
  have hrank : w.nr 191 = rank := hr
  have hkey : w.rr 94 = key := hk
  have he := Run.seq (Run.atom settledAddress s) (Run.seq (add_copies_run input 99 97 (by decide) (A.d + 4) p)
    (run_atoms input settleOps w))
  have hc : 1 + (A.d + 4 + settleOps.length) = A.d + 13 := by change 1 + (_ + 4 + 8) = _; omega
  refine ⟨t, hc ▸ he, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact ha
  · simp [t, settleOps, evalAtoms, Atom.eval, Store.ofRAM, Store.at, ramStep, evalNat, hrank]
  · change t.nm = Function.update w.nm _ rank
    simp [t, settleOps, evalAtoms, Atom.eval, Store.ofRAM, Store.at, ramStep, evalNat, ha, hrank]
  · change t.rm = Function.update w.rm _ (1 - key)
    simp [t, settleOps, evalAtoms, Atom.eval, Store.ofRAM, Store.at, ramStep, evalReal, ha, hkey]
  · intro j h99 h191 h86
    simp [t, w, p, added, settledAddress, settleOps, evalAtoms, Atom.eval, Store.ofRAM, Store.at, ramStep,
      Function.update_of_ne h99, Function.update_of_ne h191, Function.update_of_ne h86]
  · intro j hj
    simp [t, w, p, added, settledAddress, settleOps, evalAtoms, Atom.eval, Store.ofRAM, Store.at, ramStep, Function.update_of_ne hj]

theorem separated_cell_fields {k : ℕ} (A : ClockCall k) (base : ℕ) (i j : Fin A.d → ℕ) (u v x y : ℕ)
    (hu : u < A.I.graph.n) (hv : v < A.I.graph.n) (hi : ∀ r, i r < A.q) (hj : ∀ r, j r < A.q)
    (hx : x < A.d + 4) (hy : y < A.d + 4) (he : rowCell A base i u + x = rowCell A base j v + y) :
    i = j ∧ u = v ∧ x = y := by
  let m := vectorIndex A.q i * A.I.graph.n + u
  let n := vectorIndex A.q j * A.I.graph.n + v
  have hcode : (A.d + 4) * m + x = (A.d + 4) * n + y := by
    change base + 4 + (A.d + 4) * m + x = base + 4 + (A.d + 4) * n + y at he
    omega
  have hm : m = n := by
    rcases lt_trichotomy m n with h | h | h
    · have hmul := Nat.mul_le_mul_left (A.d + 4) (Nat.succ_le_of_lt h)
      rw [Nat.mul_succ] at hmul; omega
    · exact h
    · have hmul := Nat.mul_le_mul_left (A.d + 4) (Nat.succ_le_of_lt h)
      rw [Nat.mul_succ] at hmul; omega
  have hxy : x = y := by rw [hm] at hcode; omega
  change vectorIndex A.q i * A.I.graph.n + u = vectorIndex A.q j * A.I.graph.n + v at hm
  have hindex : vectorIndex A.q i = vectorIndex A.q j := by
    rcases lt_trichotomy (vectorIndex A.q i) (vectorIndex A.q j) with h | h | h
    · have hmul := Nat.mul_le_mul_right A.I.graph.n (Nat.succ_le_of_lt h)
      rw [Nat.succ_mul] at hmul; omega
    · exact h
    · have hmul := Nat.mul_le_mul_right A.I.graph.n (Nat.succ_le_of_lt h)
      rw [Nat.succ_mul] at hmul; omega
  rw [hindex] at hm
  exact ⟨vectorIndex_inj i j hi hj hindex, by omega, hxy⟩

end NearLinearRSP.TwoResources.Supplement.LayerRAM

end

section

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace NearLinearRSP.TwoResources.Supplement.LayerRAM
open Mission.Structured TableQuery

theorem pgf_effect (j : ℕ) (input : RAMInput) (s : Store) :
    let t := evalAtoms input (pgfOps j) s
    t.rm = Function.update s.rm (s.nr 49 + 4 + j) (s.rm (s.nr 190 + 2 * j + 1)) ∧
      t.nm = s.nm ∧ (∀ a, a ≠ 85 → t.nr a = s.nr a) ∧ (∀ a, a ≠ 87 → t.rr a = s.rr a) := by
  simp +contextual [pgfOps, evalAtoms, Atom.eval, Store.ofRAM, Store.at, ramStep, evalNat, Nat.add_assoc,
    Function.update_of_ne]

theorem copy_pgf_run (n addr params : ℕ) (input : RAMInput) (s : Store)
    (ha : s.nr 49 = addr) (hp : s.nr 190 = params) (hsep : addr + 4 + n ≤ params) :
    ∃ t, Run input (copyPGF n) s t (6 * n) ∧
      (∀ j < n, t.rm (addr + 4 + j) = s.rm (params + 2 * j + 1)) ∧
      (∀ a, a < addr + 4 ∨ addr + 4 + n ≤ a → t.rm a = s.rm a) ∧
      t.nm = s.nm ∧ (∀ a, a ≠ 85 → t.nr a = s.nr a) ∧ (∀ a, a ≠ 87 → t.rr a = s.rr a) := by
  induction n with
  | zero => exact ⟨s, Run.skip s, fun _ hh => (Nat.not_lt_zero _ hh).elim, fun _ _ => rfl, rfl, fun _ _ => rfl, fun _ _ => rfl⟩
  | succ n ih =>
    obtain ⟨w, hw, hd, hf, hn, hnr, hrr⟩ := ih (by omega)
    let t := evalAtoms input (pgfOps n) w
    obtain ⟨ht, htn, htnr, htrr⟩ := pgf_effect n input w
    change t.rm = _ at ht
    rw [hnr 49 (by decide), hnr 190 (by decide), ha, hp, hf _ (Or.inr (by omega))] at ht
    have hc : 6 * n + (pgfOps n).length = 6 * (n + 1) := by change 6 * n + 6 = _; omega
    refine ⟨t, hc ▸ Run.seq hw (run_atoms input (pgfOps n) w), ?_, ?_, htn.trans hn,
      fun a h => (htnr a h).trans (hnr a h), fun a h => (htrr a h).trans (hrr a h)⟩
    · intro j hj
      by_cases he : j = n
      · subst j; simp [ht]
      · simpa only [ht, Function.update_of_ne (show addr + 4 + j ≠ addr + 4 + n by omega)] using hd j (by omega)
    · intro a h
      simpa only [ht, Function.update_of_ne (show a ≠ addr + 4 + n by omega)] using hf a (by omega)

theorem write_parent_run {k : ℕ} (A : ClockCall k) (base u v params : ℕ) (i : Fin A.d → ℕ)
    (input : RAMInput) (s : Store) (hrow : s.nr 98 = rowCell A base i 0) (hu : s.nr 97 = u)
    (hv : s.nr 100 = v) (hp : s.nr 190 = params) (hsep : rowCell A base i v + 4 + A.d ≤ params) :
    let a := rowCell A base i v
    ∃ t, Run input (writeParent A.d) s t (7 * A.d + 11) ∧ t.rr 94 = s.rr 88 ∧
      t.nm = Function.update (Function.update s.nm a 2) (a + 1) u ∧
      (∀ j < A.d, t.rm (a + 4 + j) = s.rm (params + 2 * j + 1)) ∧
      (∀ x, x < a + 4 ∨ a + 4 + A.d ≤ x → t.rm x = s.rm x) ∧
      (∀ r, r ≠ 49 → r ≠ 85 → r ≠ 86 → t.nr r = s.nr r) ∧
      (∀ r, r ≠ 87 → r ≠ 94 → t.rr r = s.rr r) := by
  let p := parentStart.eval input s
  let w := added 49 100 (A.d + 4) p
  let b := evalAtoms input parentOps w
  let a := rowCell A base i v
  have ha : w.nr 49 = a := by
    simp [w, p, added, parentStart, Atom.eval, Store.ofRAM, Store.at, ramStep, hrow, hv, a, rowCell, scanAddress]
    ring
  have hbu : w.nr 97 = u := hu
  have hbn : b.nm = Function.update (Function.update s.nm a 2) (a + 1) u := by
    change b.nm = Function.update (Function.update w.nm a 2) (a + 1) u
    simp [b, parentOps, evalAtoms, Atom.eval, Store.ofRAM, Store.at, ramStep, evalNat, ha, hbu]
  obtain ⟨t, ht, hd, hf, hn, hnr, hrr⟩ := copy_pgf_run A.d a params input b (by exact ha) (by exact hp) hsep
  have hc : 1 + (A.d + 4 + (parentOps.length + 6 * A.d)) = 7 * A.d + 11 := by change 1 + (_ + 4 + (6 + 6 * _)) = _; omega
  refine ⟨t, hc ▸ Run.seq (Run.atom parentStart s) (Run.seq (add_copies_run input 49 100 (by decide) _ p)
    (Run.seq (run_atoms input parentOps w) ht)), (hrr 94 (by decide)).trans rfl, hn.trans hbn, hd, hf, ?_, ?_⟩
  · intro r h49 h85 h86
    rw [hnr r h85]
    simp [b, w, p, parentOps, parentStart, added, evalAtoms, Atom.eval, Store.ofRAM, Store.at, ramStep,
      Function.update_of_ne h86, Function.update_of_ne h49]
  · intro r h87 h94
    rw [hrr r h87]
    simp [b, w, p, parentOps, parentStart, added, evalAtoms, Atom.eval, Store.ofRAM, Store.at, ramStep,
      Function.update_of_ne h94]

end NearLinearRSP.TwoResources.Supplement.LayerRAM

end

section

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace NearLinearRSP.TwoResources.Supplement.LayerRAM
open Mission.Structured TableQuery

theorem row_end {k : ℕ} (A : ClockCall k) (base v : ℕ) (i : Fin A.d → ℕ) (hv : v ∈ incidentVertices A.I)
    (hi : ∀ r, i r < A.q) : rowCell A base i v + 4 + A.d ≤ extent A base := by
  have h := scanAddress_inside A base v (incident_valid A.I v hv) i hi (A.d + 3) (by omega)
  change rowCell A base i v + (A.d + 3) < extent A base at h
  omega

theorem ParentRecords.congr {k : ℕ} {A : ClockCall k} {base : ℕ} {i : Fin A.d → ℕ} {p : ℕ → MultiParent}
    {s t : Store} (h : ParentRecords A base i p s) (hi : ∀ r, i r < A.q)
    (hf : ∀ a < extent A base, t.nm a = s.nm a ∧ t.rm a = s.rm a) :
    ParentRecords A base i p t := by
  intro w hw
  let a := rowCell A base i w
  have hb : a + 4 + A.d ≤ extent A base := row_end A base w i hw hi
  obtain ⟨ht, hd, hg⟩ := h w hw
  refine ⟨((hf a (by omega)).1).trans ht, ((hf (a + 1) (by omega)).1).trans hd, ?_⟩
  intro u hu r
  have hr := r.isLt
  exact ((hf (a + 4 + r.val) (by omega)).2).trans (hg u hu r)

theorem seed_parent_records {k : ℕ} (A : ClockCall k) (T : MultiTable A.d) (base keys : ℕ) (i : Fin A.d → ℕ)
    (s : Store) (h : Seeded A T base keys i (incidentVertices A.I).length s) :
    ParentRecords A base i (initializeLayer A T i).parents s := by
  intro w hw
  let xs := incidentVertices A.I
  have hv : vertexAt A (xs.idxOf w) = w := Mission.Queue.slotVertex_idxOf_eq xs w hw
  obtain ⟨ht, hd, _⟩ := h (xs.idxOf w) (List.idxOf_lt_length_of_mem hw)
  rw [hv] at ht hd
  refine ⟨ht, hd, ?_⟩
  intro u hu
  simp only [initializeLayer] at hu
  split at hu
  · contradiction
  · cases hnext : nextTick A T w i <;> simp [hnext] at hu

theorem parent_records_update {k : ℕ} (A : ClockCall k) (base u v params : ℕ) (i : Fin A.d → ℕ)
    (p : ℕ → MultiParent) (s t : Store) (h : ParentRecords A base i p s)
    (hn : t.nm = Function.update (Function.update s.nm (rowCell A base i v) 2) (rowCell A base i v + 1) u)
    (hd : ∀ j < A.d, t.rm (rowCell A base i v + 4 + j) = s.rm (params + 2 * j + 1))
    (hf : ∀ a, a < rowCell A base i v + 4 ∨ rowCell A base i v + 4 + A.d ≤ a → t.rm a = s.rm a)
    (hg : ∀ r : Fin A.d, s.rm (params + 2 * r.val + 1) = clockPGF A r u v) :
    ParentRecords A base i (Function.update p v (.edge u)) t := by
  intro w hw
  let a := rowCell A base i v
  let b := rowCell A base i w
  by_cases he : w = v
  · subst w
    simp only [Function.update_self, multiParentTag, multiParentPayload]
    refine ⟨?_, ?_, ?_⟩
    · simp [hn, Function.update_of_ne (show a ≠ a + 1 by omega), a]
    · simp [hn]
    · intro z hz r
      cases hz
      exact (hd r.val r.isLt).trans (hg r)
  · obtain ⟨ht, hp, hpg⟩ := h w hw
    simp only [Function.update_of_ne he]
    have sep (x y : ℕ) (hx : x < A.d + 4) (hy : y < A.d + 4) : b + x ≠ a + y := row_disjoint A base i w v x y he hx hy
    have h0 : b ≠ a := by simpa only [Nat.add_zero] using sep 0 0 (by omega) (by omega)
    have h1 : b ≠ a + 1 := by simpa only [Nat.add_zero] using sep 0 1 (by omega) (by omega)
    have h2 : b + 1 ≠ a := by simpa only [Nat.add_zero] using sep 1 0 (by omega) (by omega)
    have h3 : b + 1 ≠ a + 1 := sep 1 1 (by omega) (by omega)
    change t.nm b = _ ∧ t.nm (b + 1) = _ ∧ _
    change t.nm = Function.update (Function.update s.nm a 2) (a + 1) u at hn
    refine ⟨by simpa only [hn, Function.update_of_ne h1, Function.update_of_ne h0] using ht,
      by simpa only [hn, Function.update_of_ne h3, Function.update_of_ne h2] using hp, ?_⟩
    intro z hz r
    have hbound : b + 4 + r.val < a + 4 ∨ a + 4 + A.d ≤ b + 4 + r.val := by
      have hr := r.isLt
      rcases Nat.lt_or_gt_of_ne he with hlt | hlt
      · have hh : b + (A.d + 4) ≤ a := row_ascending A base i w v hlt
        omega
      · have hh : a + (A.d + 4) ≤ b := row_ascending A base i v w hlt
        omega
    exact (hf _ hbound).trans (hpg z hz r)

end NearLinearRSP.TwoResources.Supplement.LayerRAM

end

section

set_option autoImplicit false
set_option maxHeartbeats 1200000

namespace NearLinearRSP.TwoResources.Supplement.LayerRAM
open Mission.Structured
open Mission.Queue (activeLeaf)

theorem probe_leaf (xs q : List ℕ) (key : ℕ → ℝ) (B W P v : ℕ) (input : RAMInput) (s : Store)
    (h : Heap B W P (activeLeaf xs q key B) s) (cfg : Config B W P s) (hB : xs.length ≤ B)
    (hv : v ∈ xs) (head : s.nr 77 = v) (index : s.nm (s.nr 141 + v) = xs.idxOf v + 1) :
    let t := evalAtoms input probeLeaf s
    t.nr 100 = v ∧ t.nr 95 = xs.idxOf v ∧ t.nr 96 = (if v ∈ q then xs.idxOf v + 1 else 0) ∧
      t.rr 92 = key v ∧ t.nm = s.nm ∧ t.rm = s.rm := by
  obtain ⟨ht, hk⟩ := heap_leaf xs q key B W P v s hB hv h
  simp [probeLeaf, evalAtoms, Atom.eval, Store.at, Store.ofRAM, ramStep, evalNat, head, index,
    cfg.capacity, cfg.winnerBase, ht, hk]

theorem probe_index (xs : List ℕ) (n base array v : ℕ) (s : Store)
    (h : Mission.Preprocess.ActiveRep n base array xs s) (hv : v ∈ xs) :
    s.nm (s.nr 141 + v) = xs.idxOf v + 1 := by
  rw [h.base_reg]
  apply h.index
  simp [List.getElem?_idxOf, hv]

end NearLinearRSP.TwoResources.Supplement.LayerRAM

end

section

set_option autoImplicit false
set_option maxHeartbeats 1500000

namespace NearLinearRSP.TwoResources.Supplement.LayerRAM
open Mission.Preprocess Classical

noncomputable def offer {d : ℕ} (u v : ℕ) (b : ℝ) (S : MultiLayer d) : MultiLayer d :=
  if b < S.keys v then {S with keys := Function.update S.keys v b, parents := Function.update S.parents v (.edge u)} else S

theorem offer_comm {d : ℕ} (u x y : ℕ) (b c : ℝ) (S : MultiLayer d) (hne : x ≠ y) :
    offer u y c (offer u x b S) = offer u x b (offer u y c S) := by
  by_cases hb : b < S.keys x <;> by_cases hc : c < S.keys y <;>
    simp [offer, hb, hc, Function.update_of_ne hne, Function.update_of_ne hne.symm]
  constructor <;> exact Function.update_comm hne _ _ _

theorem relax_as_offer {k : ℕ} (A : ClockCall k) (i : Fin A.d → ℕ) (u : ℕ) (S : MultiLayer A.d) (e : ℕ × ℕ) :
    relax A i u S e = if e.1 = u ∧ e.2 ∈ S.queue then offer u e.2 (expectation A S.table u e.2 i) S else S := by
  rfl

theorem relax_comm {k : ℕ} (A : ClockCall k) (i : Fin A.d → ℕ) (u : ℕ) (S : MultiLayer A.d) (e f : ℕ × ℕ) :
    relax A i u (relax A i u S e) f = relax A i u (relax A i u S f) e := by
  by_cases he : e.1 = u ∧ e.2 ∈ S.queue <;> by_cases hf : f.1 = u ∧ f.2 ∈ S.queue
  · by_cases h : e.2 = f.2
    · have heq : e = f := Prod.ext (he.1.trans hf.1.symm) h
      rw [heq]
    · rw [relax_as_offer A i u (relax A i u S e) f, relax_as_offer A i u (relax A i u S f) e,
        relax_queue, relax_queue, relax_table, relax_table, if_pos hf, if_pos he,
        relax_as_offer A i u S e, relax_as_offer A i u S f, if_pos he, if_pos hf]
      exact offer_comm _ _ _ _ _ _ h
  · rw [relax_as_offer A i u (relax A i u S e) f, relax_queue, if_neg hf, relax_as_offer A i u S f, if_neg hf]
  · rw [relax_as_offer A i u (relax A i u S f) e, relax_queue, if_neg he, relax_as_offer A i u S e, if_neg he]
  · simp only [relax_as_offer A i u S e, relax_as_offer A i u S f, if_neg he, if_neg hf]

noncomputable def guarded {k : ℕ} (A : ClockCall k) (i : Fin A.d → ℕ) (u : ℕ) (S : MultiLayer A.d) (e : ℕ × ℕ) :=
  if e ∈ callEdges A then relax A i u S e else S

theorem guarded_comm {k : ℕ} (A : ClockCall k) (i : Fin A.d → ℕ) (u : ℕ) (S : MultiLayer A.d) (e f : ℕ × ℕ) :
    guarded A i u (guarded A i u S e) f = guarded A i u (guarded A i u S f) e := by
  by_cases he : e ∈ callEdges A <;> by_cases hf : f ∈ callEdges A <;>
    simp [guarded, he, hf, relax_comm A i u S e f]

theorem filter_calls {k : ℕ} (A : ClockCall k) :
    A.I.graph.edges.filter (fun e => decide (e ∈ callEdges A)) = callEdges A := by
  unfold callEdges usableEdges
  rw [List.filter_filter]
  apply List.filter_congr
  intro e he
  simp [he]

theorem linked_relaxations {k : ℕ} (A : ClockCall k) (i : Fin A.d → ℕ) (u : ℕ) (S : MultiLayer A.d) :
    (outgoingIndices (lengthInstance A.I) A.I.graph.edges.length u).foldl
      (fun s j => guarded A i u s (edgeAt (lengthInstance A.I) j)) S = (callEdges A).foldl (relax A i u) S := by
  let J := lengthInstance A.I
  let es := outgoingEdges J u
  have hm : (outgoingIndices J A.I.graph.edges.length u).map (edgeAt J) = es.reverse := outgoingIndices_edges J u
  have hrev : es.reverse.foldl (guarded A i u) S = es.foldl (guarded A i u) S :=
    (List.reverse_perm es).foldl_eq' (fun e _ f _ t => guarded_comm A i u t e f) S
  have hstep (t : MultiLayer A.d) (e : ℕ × ℕ) :
      (if e.1 == u then guarded A i u t e else t) = guarded A i u t e := by
    by_cases h : e.1 = u
    · simp [h]
    · simp [guarded, relax, h]
  calc
    _ = ((outgoingIndices J A.I.graph.edges.length u).map (edgeAt J)).foldl (guarded A i u) S := by rw [List.foldl_map]
    _ = es.foldl (guarded A i u) S := by rw [hm, hrev]
    _ = A.I.graph.edges.foldl (guarded A i u) S := by
      simp only [es, outgoingEdges, List.foldl_filter, hstep, J, lengthInstance]
    _ = _ := by
      rw [← filter_calls A, List.foldl_filter]
      congr 1
      funext t e
      simp only [guarded, decide_eq_true_eq]

end NearLinearRSP.TwoResources.Supplement.LayerRAM

end

section

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace NearLinearRSP.TwoResources.Supplement.LayerRAM
open Mission.Structured TableQuery
open Mission.Queue (activeLeaf)

structure CompareFrame (W a d : ℕ) (s t : Store) : Prop where
  nat : ∀ x < W, x ≠ a → x ≠ a + 1 → t.nm x = s.nm x
  real : ∀ x < W, x < a + 4 ∨ a + 4 + d ≤ x → t.rm x = s.rm x

theorem compare_edge_run {k : ℕ} (A : ClockCall k) (base params B W P u v : ℕ) (i : Fin A.d → ℕ)
    (S : MultiLayer A.d) (score : ℝ) (input : RAMInput) (s : Store)
    (hv : v ∈ incidentVertices A.I) (hq : v ∈ S.queue) (hi : ∀ r, i r < A.q)
    (hB : (incidentVertices A.I).length ≤ B) (hsep : extent A base ≤ params) (hW : params ≤ W)
    (cfg : Config B W P s) (heap : Heap B W P (activeLeaf (incidentVertices A.I) S.queue S.keys B) s)
    (parents : ParentRecords A base i S.parents s) (hu : s.nr 97 = u) (hhead : s.nr 100 = v)
    (hrow : s.nr 98 = rowCell A base i 0) (hp : s.nr 190 = params)
    (hj : s.nr 95 = (incidentVertices A.I).idxOf v) (ht : s.nr 96 = (incidentVertices A.I).idxOf v + 1)
    (hscore : s.rr 88 = score) (hkey : s.rr 92 = S.keys v)
    (hpg : ∀ r : Fin A.d, s.rm (params + 2 * r.val + 1) = clockPGF A r u v) :
    let U := offer u v score S
    ∃ t n, Run input (compareEdge A.d) s t n ∧
      Heap B W P (activeLeaf (incidentVertices A.I) U.queue U.keys B) t ∧
      ParentRecords A base i U.parents t ∧ CompareFrame W (rowCell A base i v) A.d s t ∧
      n ≤ 7 * A.d + 19 * Nat.clog 2 (2 * B) + 26 := by
  dsimp only
  let xs := incidentVertices A.I
  let a := rowCell A base i v
  have ha : a + 4 + A.d ≤ extent A base := row_end A base v i hv hi
  by_cases hb : score < S.keys v
  · have hg : (Guard.real .lt 88 92).eval s = true := by simp [Guard.eval, realTest, hscore, hkey, hb]
    obtain ⟨p, hr, hr94, hn, hd, hf, hnr, _⟩ := write_parent_run A base u v params i input s hrow hu hhead hp (by omega)
    change p.nm = Function.update (Function.update s.nm a 2) (a + 1) u at hn
    have hnat (x : ℕ) (h0 : x ≠ a) (h1 : x ≠ a + 1) : p.nm x = s.nm x := by
      simp only [hn, Function.update_of_ne h1, Function.update_of_ne h0]
    have hpp : ParentRecords A base i (Function.update S.parents v (.edge u)) p :=
      parent_records_update A base u v params i S.parents s p parents hn hd hf hpg
    have hfar (x : ℕ) (hx : W ≤ x) : p.nm x = s.nm x ∧ p.rm x = s.rm x :=
      ⟨hnat x (by omega) (by omega), hf x (Or.inr (by omega))⟩
    have hHeap := heap.congr (fun j _ => hfar _ (by omega)) (fun j _ => (hfar _ (by have := heap.disjoint; omega)).1)
    have reg (j : ℕ) (hl : 90 ≤ j) := hnr j (by omega) (by omega) (by omega)
    have hCfg : Config B W P p := ⟨(reg 180 (by omega)).trans cfg.winnerBase, (reg 181 (by omega)).trans cfg.parentBase,
      (reg 188 (by omega)).trans cfg.capacity⟩
    obtain ⟨t, n, he, hnew, hkeep, hc⟩ := decrease_heap xs S.queue S.keys v score B W P input p
      (incident_nodup A.I) hv hq hB hCfg hHeap ((reg 95 (by omega)).trans hj) ((reg 96 (by omega)).trans ht) (hr94.trans hscore)
    have hpar := hpp.congr hi (fun x hx => hkeep x (Or.inl (by omega)))
    simp only [offer, if_pos hb]
    refine ⟨t, _, Run.branchTrue hg (Run.seq hr he), hnew, hpar, ⟨?_, ?_⟩, by omega⟩
    · intro x hx h0 h1
      exact ((hkeep x (Or.inl hx)).1).trans (hnat x h0 h1)
    · intro x hx hs
      exact ((hkeep x (Or.inl hx)).2).trans (hf x hs)
  · have hg : (Guard.real .lt 88 92).eval s = false := by simp [Guard.eval, realTest, hscore, hkey, hb]
    simp only [offer, if_neg hb]
    exact ⟨s, _, Run.branchFalse hg (Run.skip s), heap, parents, ⟨fun _ _ _ _ => rfl, fun _ _ _ => rfl⟩, by omega⟩

end NearLinearRSP.TwoResources.Supplement.LayerRAM

end

section

set_option autoImplicit false
set_option maxHeartbeats 1500000

namespace NearLinearRSP.TwoResources.Supplement.EdgeRAM
open Mission.Structured Classical

def Pass (input : RAMInput) (base r : ℕ) := input.reals (r + 1) = 0 → input.reals (base + (r + 1)) = 0

theorem test_fields (input : RAMInput) (r : ℕ) (s : Store) :
    let t := evalAtoms input (loadTest r) s
    t.nr 70 = s.nr 70 ∧ t.nr 71 = s.nr 71 ∧ t.rr 74 = s.rr 74 ∧
      t.rr 72 = input.reals (r + 1) ∧ t.rr 73 = input.reals (s.nr 70 + (r + 1)) := by
  simp [loadTest, evalAtoms, Atom.eval, Store.ofRAM, Store.at, ramStep, evalNat]

theorem test_run (input : RAMInput) (r : ℕ) (s : Store) (hz : s.rr 74 = 0) :
    ∃ t n, Run input (test r) s t n ∧
      t.nr 71 = (if Pass input (s.nr 70) r then s.nr 71 else 0) ∧
      t.nr 70 = s.nr 70 ∧ t.rr 74 = 0 ∧ n ≤ 8 := by
  classical
  let p := evalAtoms input (loadTest r) s
  obtain ⟨ha, hflag, hzero, hb, hw⟩ := test_fields input r s
  have he : Run input (.atoms (loadTest r)) s p 4 := run_atoms input _ _
  have h0 : p.rr 74 = 0 := hzero.trans hz
  by_cases hbud : input.reals (r + 1) = 0
  · have g₁ : (Guard.real .eq 72 74).eval p = true := by simp [Guard.eval, realTest, p, hb, h0, hbud]
    by_cases hval : input.reals (s.nr 70 + (r + 1)) = 0
    · have g₂ : (Guard.real .eq 73 74).eval p = true := by simp [Guard.eval, realTest, p, hw, h0, hval]
      exact ⟨p, _, Run.seq he (Run.branchTrue g₁ (Run.branchTrue g₂ (Run.skip p))),
        by simpa [Pass, hval] using hflag, ha, h0, by decide⟩
    · have g₂ : (Guard.real .eq 73 74).eval p = false := by simp [Guard.eval, realTest, p, hw, h0, hval]
      exact ⟨_, _, Run.seq he (Run.branchTrue g₁ (Run.branchFalse g₂ (Run.atom reject p))),
        by simp [Pass, hbud, hval, reject, Atom.eval, Store.ofRAM, Store.at, ramStep], ha, h0, by decide⟩
  · have g₁ : (Guard.real .eq 72 74).eval p = false := by simp [Guard.eval, realTest, p, hb, h0, hbud]
    exact ⟨p, _, Run.seq he (Run.branchFalse g₁ (Run.skip p)),
      by simpa [Pass, hbud] using hflag, ha, h0, by decide⟩

theorem tests_run (input : RAMInput) (rs : List ℕ) (s : Store) (hz : s.rr 74 = 0) :
    ∃ t n, Run input (tests rs) s t n ∧
      t.nr 71 = (if ∀ r ∈ rs, Pass input (s.nr 70) r then s.nr 71 else 0) ∧ n ≤ 8 * rs.length := by
  classical
  induction rs generalizing s with
  | nil => exact ⟨s, 0, Run.skip s, by simp, by simp⟩
  | cons r rs ih =>
    obtain ⟨p, n, hp, hf, hb, h0, hn⟩ := test_run input r s hz
    obtain ⟨t, m, ht, hflag, hm⟩ := ih p h0
    rw [hb, hf] at hflag
    refine ⟨t, n + m, Run.seq hp ht, ?_, by simp only [List.length_cons]; omega⟩
    by_cases h1 : Pass input (s.nr 70) r <;> by_cases h2 : ∀ j ∈ rs, Pass input (s.nr 70) j <;>
      simpa [List.forall_mem_cons, h1, h2] using hflag

theorem input_passes {k : ℕ} (I : MultiInstance k) (ε : ℝ) (i : ℕ) (e : ℕ × ℕ)
    (he : I.graph.edges[i]? = some e) :
    (∀ j ∈ List.range (k - 1), Pass (multiInput I ε) (InputValues.row k i) j) ↔
      ∀ r, I.budget r = 0 → I.cost r e.1 e.2 = 0 := by
  have one (r : Fin (k - 1)) : Pass (multiInput I ε) (InputValues.row k i) r.val ↔
      (I.budget r = 0 → I.cost r e.1 e.2 = 0) := by
    simp only [Pass, InputValues.budget_read I ε r, InputValues.row_cost I ε i e he r, NNReal.coe_eq_zero]
  exact ⟨fun h r => (one r).mp (h r.val (List.mem_range.mpr r.isLt)), fun h j hj =>
    (one ⟨j, List.mem_range.mp hj⟩).mpr (h _)⟩

end NearLinearRSP.TwoResources.Supplement.EdgeRAM

end

section

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace NearLinearRSP.TwoResources.Supplement.EdgeRAM
open Mission.Structured Classical

noncomputable def loaded (k : ℕ) (input : RAMInput) (s : Store) :=
  lengthOp.eval input (TableQuery.added 70 75 k (evalAtoms input (baseOps k) s))

theorem read_edge {k : ℕ} (I : MultiInstance k) (hk : 0 < k) (ε : ℝ) (i : ℕ) (e : ℕ × ℕ)
    (he : I.graph.edges[i]? = some e) (s : Store) (hi : s.nr 75 = i) :
    let p := loaded k (multiInput I ε) s
    Run (multiInput I ε) (readCmd k) s p (k + 12) ∧ p.nr 70 = InputValues.row k i ∧
      p.nr 71 = 1 ∧ p.nr 76 = e.1 ∧ p.nr 77 = e.2 ∧ p.rr 78 = I.length e.1 e.2 ∧
      p.nr 74 = 0 ∧ p.rr 74 = 0 ∧ p.nr 79 = s.nr 79 := by
  let input := multiInput I ε
  obtain ⟨hu, hv⟩ := InputValues.edge_endpoints I ε i e he
  have hl := InputValues.row_length I hk ε i e he
  have hr := Run.seq (run_atoms input (baseOps k) s) (Run.seq
    (TableQuery.add_copies_run input 70 75 (by decide) k _) (Run.atom lengthOp _))
  have hc : (baseOps k).length + (k + 1) = k + 12 := by change 11 + (k + 1) = _; omega
  refine ⟨hc ▸ hr, ?_⟩
  change (multiInput I ε).reals (k + k * i) = _ at hl
  simp [loaded, TableQuery.added, lengthOp, baseOps, evalAtoms, Atom.eval, Store.ofRAM, Store.at, ramStep,
    evalNat, hi, ← two_mul, hu, hv, InputValues.row, hl]

theorem restrictions_run (input : RAMInput) (s : Store) (hflag : s.nr 71 = 1) (hz : s.nr 74 = 0) (hr : s.rr 74 = 0) :
    ∃ t n, Run input restrictions s t n ∧
      t.nr 71 = (if s.nr 76 ≠ s.nr 77 ∧ (s.nr 79 = 0 ∨ s.rr 78 = 0) then 1 else 0) ∧ n ≤ 5 := by
  by_cases he : s.nr 76 = s.nr 77
  · exact ⟨_, _, Run.branchTrue (by simp [Guard.eval, natTest, he]) (Run.atom reject s),
      by simp [he, reject, Atom.eval, Store.ofRAM, Store.at, ramStep], by decide⟩
  · have g1 : (Guard.nat .eq 76 77).eval s = false := by simp [Guard.eval, natTest, he]
    by_cases hm : s.nr 79 = 0
    · exact ⟨s, _, Run.branchFalse g1 (Run.branchTrue (by simp [Guard.eval, natTest, hm, hz]) (Run.skip s)),
        by simpa [he, hm] using hflag, by decide⟩
    · have g2 : (Guard.nat .eq 79 74).eval s = false := by simp [Guard.eval, natTest, hz, hm]
      by_cases hl : s.rr 78 = 0
      · exact ⟨s, _, Run.branchFalse g1 (Run.branchFalse g2 (Run.branchTrue
          (by simp [Guard.eval, realTest, hr, hl]) (Run.skip s))), by simpa [he, hl] using hflag, by decide⟩
      · exact ⟨_, _, Run.branchFalse g1 (Run.branchFalse g2 (Run.branchFalse
          (by simp [Guard.eval, realTest, hr, hl]) (Run.atom reject s))),
          by simp [he, hl, hm, reject, Atom.eval, Store.ofRAM, Store.at, ramStep], by decide⟩

theorem tests_registers (rs : List ℕ) (a : ℕ) (h71 : a ≠ 71) (h72 : a ≠ 72) : a ∉ (tests rs).natWrites := by
  induction rs with
  | nil => simp [tests, Cmd.natWrites]
  | cons r rs ih =>
    have h : a ∉ (test r).natWrites := by
      simp [test, loadTest, reject, Cmd.atoms, Cmd.natWrites, Atom.natWrites, h71, h72]
    simpa [tests, Cmd.natWrites, h, ih]

theorem tests_real_registers (rs : List ℕ) (a : ℕ) (h72 : a ≠ 72) (h73 : a ≠ 73) : a ∉ (tests rs).realWrites := by
  induction rs with
  | nil => simp [tests, Cmd.realWrites]
  | cons r rs ih =>
    have h : a ∉ (test r).realWrites := by
      simp [test, loadTest, reject, Cmd.atoms, Cmd.realWrites, Atom.realWrites, h72, h73]
    simpa [tests, Cmd.realWrites, h, ih]

theorem edge_run {k : ℕ} (A : ClockCall k) (hk : 0 < k) (ε : ℝ) (i : ℕ) (e : ℕ × ℕ)
    (he : A.I.graph.edges[i]? = some e) (s : Store) (hi : s.nr 75 = i) (ht : s.nr 79 = if A.zeroOnly then 1 else 0) :
    ∃ t n, Run (multiInput A.I ε) (loadEdge k) s t n ∧
      t.nr 71 = (if e ∈ callEdges A then 1 else 0) ∧ t.nr 70 = InputValues.row k i ∧
      t.nr 76 = e.1 ∧ t.nr 77 = e.2 ∧ t.rr 78 = A.I.length e.1 e.2 ∧ n ≤ 9 * k + 17 := by
  let input := multiInput A.I ε
  let p := loaded k input s
  obtain ⟨hp, hrow, hflag, hu, hv, hl, hz, hr, hmode⟩ := read_edge A.I hk ε i e he s hi
  obtain ⟨u, c, htest, hm, hc⟩ := restrictions_run input p hflag hz hr
  have urow : u.nr 70 = InputValues.row k i := (htest.nat_frame 70 (by decide)).trans hrow
  have urz : u.rr 74 = 0 := (htest.real_frame 74 (by decide)).trans hr
  obtain ⟨t, n, hs, hfinal, hn⟩ := tests_run input (List.range (k - 1)) u urz
  simp only [input, urow, input_passes A.I ε i e he, hm] at hfinal
  have hmem : e ∈ A.I.graph.edges := List.mem_of_getElem? he
  have natFr (j : ℕ) (h1 : j ≠ 71) (h2 : j ≠ 72) : t.nr j = u.nr j := hs.nat_frame j (tests_registers _ j h1 h2)
  refine ⟨t, _, Run.seq hp (Run.seq htest hs), ?_, (natFr 70 (by decide) (by decide)).trans urow,
    (natFr 76 (by decide) (by decide)).trans ((htest.nat_frame 76 (by decide)).trans hu),
    (natFr 77 (by decide) (by decide)).trans ((htest.nat_frame 77 (by decide)).trans hv),
    (hs.real_frame 78 (tests_real_registers _ 78 (by decide) (by decide))).trans ((htest.real_frame 78 (by decide)).trans hl), ?_⟩
  · rw [hfinal]
    change p.nr 76 = _ at hu
    change p.nr 77 = _ at hv
    change p.nr 79 = _ at hmode
    change p.rr 78 = _ at hl
    rw [hu, hv, hl, hmode, ht]
    cases hm : A.zeroOnly <;> simp [callEdges, usableEdges, hmem, hm, NNReal.coe_eq_zero] <;> split_ifs <;> tauto
  · simp only [List.length_range] at hn
    omega

end NearLinearRSP.TwoResources.Supplement.EdgeRAM

end

section

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace NearLinearRSP.TwoResources.Supplement.EdgeRAM
open Mission.Structured

structure Rates {k : ℕ} (A : ClockCall k) (i params : ℕ) (s : Store) : Prop where
  start : s.nr 1 = params
  row : s.nr 70 = InputValues.row k i
  zero : s.nr 74 = 0
  limit : s.rr 80 = (A.q : ℝ)
  denominator : s.rr 81 = 1 + A.δ / 2
  threshold : s.rr 82 = A.L
  decay : s.rr 83 = clockZ A - 1
  coordinates : ∀ r : Fin A.d, s.nm (8 + r.val) = (A.coords.get r).val

theorem rates_frame {k : ℕ} {A : ClockCall k} {i params : ℕ} {s t : Store} {input : RAMInput} {j n : ℕ}
    (h : Rates A i params s) (hr : Run input (momentLane j) s t n) : Rates A i params t := by
  have hn (a : ℕ) (ha : a < 76) : t.nr a = s.nr a := hr.nat_frame a (by
    simp [momentLane, laneRead, momentOps, budgetCmd, Cmd.atoms, Cmd.natWrites, Atom.natWrites]; omega)
  have hrr (a : ℕ) (ha : a < 84) : t.rr a = s.rr a := hr.real_frame a (by
    simp [momentLane, laneRead, momentOps, budgetCmd, Cmd.atoms, Cmd.realWrites, Atom.realWrites]; omega)
  exact ⟨(hn _ (by decide)).trans h.start, (hn _ (by decide)).trans h.row, (hn _ (by decide)).trans h.zero,
    (hrr _ (by decide)).trans h.limit, (hrr _ (by decide)).trans h.denominator, (hrr _ (by decide)).trans h.threshold,
    (hrr _ (by decide)).trans h.decay, fun r => (congrFun (hr.natMemory_frame rfl) _).trans (h.coordinates r)⟩

theorem read_budget {k : ℕ} (A : ClockCall k) (ε : ℝ) (r : Fin k) (s : Store)
    (hz : s.nr 74 = 0) (hc : s.nr 76 = r.val) (hL : s.rr 82 = A.L) :
    ∃ n, Run (multiInput A.I ε) budgetCmd s {s with rr := Function.update s.rr 84 (coordinateBudget A.I A.L r)} n ∧ n ≤ 3 := by
  by_cases he : r.val = 0
  · let a : Atom := ⟨.realCopy 84 82, trivial⟩
    have hh : a.eval (multiInput A.I ε) s = {s with rr := Function.update s.rr 84 (coordinateBudget A.I A.L r)} := by
      simp [a, Atom.eval, Store.ofRAM, Store.at, ramStep, hL, coordinateBudget, he]
    exact ⟨3, Run.branchTrue (by simp [Guard.eval, natTest, hc, he, hz]) (hh ▸ Run.atom a s), by decide⟩
  · let a : Atom := ⟨.inputReal 84 76, trivial⟩
    have hh : a.eval (multiInput A.I ε) s = {s with rr := Function.update s.rr 84 (coordinateBudget A.I A.L r)} := by
      simp [a, Atom.eval, Store.ofRAM, Store.at, ramStep, hc, coordinateBudget, multiInput, he, r.isLt]
    exact ⟨2, Run.branchFalse (by simp [Guard.eval, natTest, hc, he, hz]) (hh ▸ Run.atom a s), by decide⟩

theorem moment_lane_run {k : ℕ} (A : ClockCall k) (ε : ℝ) (i params : ℕ) (e : ℕ × ℕ)
    (he : A.I.graph.edges[i]? = some e) (r : Fin A.d) (s : Store) (h : Rates A i params s) :
    ∃ t n, Run (multiInput A.I ε) (momentLane r.val) s t n ∧ Rates A i params t ∧
      t.rm = Function.update (Function.update s.rm (params + 2 * r.val) (clockMean A r e.1 e.2))
        (params + 2 * r.val + 1) (clockPGF A r e.1 e.2) ∧ n ≤ 18 := by
  let input := multiInput A.I ε
  let p := evalAtoms input (laneRead r.val) s
  let v := {p with rr := Function.update p.rr 84 (coordinateBudget A.I A.L (A.coords.get r))}
  have hidx : p.nr 76 = (A.coords.get r).val := by
    simp [p, laneRead, evalAtoms, Atom.eval, Store.ofRAM, Store.at, ramStep, h.coordinates r]
  have hweight : p.rr 85 = coordinateWeight A.I (A.coords.get r) e.1 e.2 := by
    simpa [p, laneRead, evalAtoms, Atom.eval, Store.ofRAM, Store.at, ramStep, evalNat, h.row, h.coordinates r]
      using InputValues.row_coordinate A.I ε i e he (A.coords.get r)
  have hh : p.nr 1 = params := h.start
  have hq : p.rr 80 = (A.q : ℝ) := h.limit
  have hden : p.rr 81 = 1 + A.δ / 2 := h.denominator
  have hdecay : p.rr 83 = clockZ A - 1 := h.decay
  obtain ⟨c, hb, hc⟩ := read_budget A ε (A.coords.get r) p h.zero hidx h.threshold
  let t := evalAtoms input (momentOps r.val) v
  have hrun : Run input (momentLane r.val) s t (4 + (c + 11)) :=
    Run.seq (run_atoms input (laneRead r.val) s) (Run.seq hb (run_atoms input (momentOps r.val) v))
  refine ⟨t, _, hrun, rates_frame h hrun, ?_, by omega⟩
  simp [t, v, momentOps, evalAtoms, Atom.eval, Store.ofRAM, Store.at, ramStep, evalNat, evalReal,
    hq, hh, hdecay, hden, hweight, clockPGF, clockMean, clockRate]
  rfl

end NearLinearRSP.TwoResources.Supplement.EdgeRAM

end

section

set_option autoImplicit false
set_option maxHeartbeats 1400000

namespace NearLinearRSP.TwoResources.Supplement.EdgeRAM
open Mission.Structured

theorem moments_run {k : ℕ} (A : ClockCall k) (ε : ℝ) (i params : ℕ) (e : ℕ × ℕ)
    (he : A.I.graph.edges[i]? = some e) (n : ℕ) (hn : n ≤ A.d) (s : Store) (h : Rates A i params s) :
    ∃ t c, Run (multiInput A.I ε) (moments n) s t c ∧ Rates A i params t ∧
      (∀ r : Fin A.d, r.val < n → t.rm (params + 2 * r.val) = clockMean A r e.1 e.2 ∧
        t.rm (params + 2 * r.val + 1) = clockPGF A r e.1 e.2) ∧
      (∀ a, a < params ∨ params + 2 * n ≤ a → t.rm a = s.rm a) ∧ t.nm = s.nm ∧ c ≤ 18 * n := by
  induction n with
  | zero =>
    exact ⟨s, 0, Run.skip s, h, fun _ hlt => (Nat.not_lt_zero _ hlt).elim, fun _ _ => rfl, rfl, by omega⟩
  | succ n ih =>
    obtain ⟨p, m, hp, hpr, hmeans, hframe, hpn, hcm⟩ := ih (by omega)
    let j : Fin A.d := ⟨n, by omega⟩
    obtain ⟨t, c, ht, htr, hwrite, hcc⟩ := moment_lane_run A ε i params e he j p hpr
    change t.rm = Function.update (Function.update p.rm (params + 2 * n) (clockMean A j e.1 e.2))
      (params + 2 * n + 1) (clockPGF A j e.1 e.2) at hwrite
    refine ⟨t, m + c, Run.seq hp ht, htr, ?_, ?_, (ht.natMemory_frame rfl).trans hpn, by omega⟩
    · intro r hr
      by_cases heq : r.val = n
      · have hrj : r = j := Fin.ext heq
        subst r
        simp [j, hwrite]
      · obtain ⟨ha, hb⟩ := hmeans r (by omega)
        simp [hwrite, Function.update_of_ne (show params + 2 * r.val ≠ params + 2 * n by omega),
          Function.update_of_ne (show params + 2 * r.val ≠ params + 2 * n + 1 by omega),
          Function.update_of_ne (show params + 2 * r.val + 1 ≠ params + 2 * n by omega),
          Function.update_of_ne (show params + 2 * r.val + 1 ≠ params + 2 * n + 1 by omega), ha, hb]
    · intro a ha
      simpa only [hwrite, Function.update_of_ne (show a ≠ params + 2 * n + 1 by omega),
        Function.update_of_ne (show a ≠ params + 2 * n by omega)] using hframe a (by omega)

theorem nat_effect (r : ℕ) (input : RAMInput) (s : Store) :
    let t := evalAtoms input (natOps r) s
    t.nm = Function.update (Function.update s.nm (s.nr 1 + 2 * r) (s.nr 57 - s.nr (TableQuery.stateReg r)))
      (s.nr 1 + 2 * r + 1) (s.nr (TableQuery.strideReg r)) ∧ t.rm = s.rm ∧ t.rr = s.rr ∧
      (∀ a, a ≠ 84 → a ≠ 85 → a ≠ 86 → t.nr a = s.nr a) := by
  have hl := TableQuery.stride_large r
  have h0 : TableQuery.strideReg r ≠ 84 := by omega
  have h1 : TableQuery.strideReg r ≠ 85 := by omega
  have h2 : TableQuery.strideReg r ≠ 86 := by omega
  have h3 : TableQuery.stateReg r ≠ 84 := by have := TableQuery.state_large r; omega
  simp +contextual [natOps, evalAtoms, Atom.eval, Store.ofRAM, Store.at, ramStep, evalNat, h0, h1, h2, h3]

theorem limits_run (d : ℕ) (input : RAMInput) (s : Store) :
    ∃ t, Run input (limits d) s t (7 * d) ∧ t.rr = s.rr ∧ t.rm = s.rm ∧
      (∀ a, a ≠ 84 → a ≠ 85 → a ≠ 86 → t.nr a = s.nr a) ∧
      (∀ r < d, t.nm (s.nr 1 + 2 * r) = s.nr 57 - s.nr (TableQuery.stateReg r) ∧
        t.nm (s.nr 1 + 2 * r + 1) = s.nr (TableQuery.strideReg r)) ∧
      ∀ a, a < s.nr 1 ∨ s.nr 1 + 2 * d ≤ a → t.nm a = s.nm a := by
  induction d with
  | zero => exact ⟨s, Run.skip s, rfl, rfl, fun _ _ _ _ => rfl, fun _ h => (Nat.not_lt_zero _ h).elim, fun _ _ => rfl⟩
  | succ d ih =>
    obtain ⟨p, he, hpr, hpm, hp, hdata, hframe⟩ := ih
    let t := evalAtoms input (natOps d) p
    obtain ⟨hmem, hreal, hrr, hregs⟩ := nat_effect d input p
    have high (a : ℕ) (ha : 100 ≤ a) := hp a (by omega) (by omega) (by omega)
    have h₁ := hp 1 (by decide) (by decide) (by decide)
    have hq := hp 57 (by decide) (by decide) (by decide)
    rw [h₁, hq, high _ (TableQuery.state_large d), high _ (TableQuery.stride_large d)] at hmem
    refine ⟨t, by simpa only [limits, t, Nat.mul_succ, show (natOps d).length = 7 from rfl] using Run.seq he (run_atoms input (natOps d) p),
      hrr.trans hpr, hreal.trans hpm, fun a h0 h1 h2 => (hregs a h0 h1 h2).trans (hp a h0 h1 h2), ?_, ?_⟩
    · intro r hr
      by_cases hrd : r = d
      · subst r
        simp [t, hmem]
      · obtain ⟨hu, hv⟩ := hdata r (by omega)
        simp [t, hmem, Function.update_of_ne (show s.nr 1 + 2 * r ≠ s.nr 1 + 2 * d by omega),
          Function.update_of_ne (show s.nr 1 + 2 * r ≠ s.nr 1 + 2 * d + 1 by omega),
          Function.update_of_ne (show s.nr 1 + 2 * r + 1 ≠ s.nr 1 + 2 * d by omega),
          Function.update_of_ne (show s.nr 1 + 2 * r + 1 ≠ s.nr 1 + 2 * d + 1 by omega), hu, hv]
    · intro a ha
      simpa only [t, hmem, Function.update_of_ne (show a ≠ s.nr 1 + 2 * d + 1 by omega),
        Function.update_of_ne (show a ≠ s.nr 1 + 2 * d by omega)] using hframe a (by omega)

end NearLinearRSP.TwoResources.Supplement.EdgeRAM

end

section

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace NearLinearRSP.TwoResources.Supplement.RegisterShift
open Mission.Structured

def view (b : ℕ) (s : Store) : Store :=
  ⟨fun a => s.nr (b + a), fun a => s.rr (b + a), s.nm, s.rm⟩

structure Below (b : ℕ) (s t : Store) : Prop where
  nat : ∀ a < b, t.nr a = s.nr a
  real : ∀ a < b, t.rr a = s.rr a

theorem Below.refl (b : ℕ) (s : Store) : Below b s s := ⟨fun _ _ => rfl, fun _ _ => rfl⟩
theorem Below.trans {b : ℕ} {s t u : Store} (h : Below b s t) (g : Below b t u) : Below b s u :=
  ⟨fun a ha => (g.nat a ha).trans (h.nat a ha), fun a ha => (g.real a ha).trans (h.real a ha)⟩

theorem view_update {α : Type} (f : ℕ → α) (b x : ℕ) (v : α) :
    (fun j => Function.update f (b + x) v (b + j)) = Function.update (fun j => f (b + j)) x v := by
  funext j
  by_cases h : j = x
  · subst j; simp
  · simp [Function.update_of_ne h, Function.update_of_ne (show b + j ≠ b + x by omega)]

theorem view_atom (b : ℕ) (a : Atom) (input : RAMInput) (s : Store) :
    view b ((atom b a).eval input s) = a.eval input (view b s) := by
  rcases a with ⟨i, hi⟩
  cases i <;> try contradiction
  all_goals simp [view, atom, instr, Atom.eval, Store.ofRAM, Store.at, ramStep, view_update]

theorem below_atom (b : ℕ) (a : Atom) (input : RAMInput) (s : Store) : Below b s ((atom b a).eval input s) := by
  rcases a with ⟨i, hi⟩
  cases i <;> try contradiction
  all_goals constructor <;> intro j hj <;>
    simp [atom, instr, Atom.eval, Store.ofRAM, Store.at, ramStep, Function.update_apply]
  all_goals intro he; omega

theorem guard_view (b : ℕ) (g : Guard) (s : Store) : (guardAt b g).eval s = g.eval (view b s) := by
  cases g <;> rfl

theorem transport {input : RAMInput} {c : Cmd} {s t : Store} {n : ℕ} (h : Run input c s t n)
    (b : ℕ) (x : Store) (hx : view b x = s) :
    ∃ y, Run input (cmd b c) x y n ∧ view b y = t ∧ Below b x y := by
  induction h generalizing x with
  | skip s => exact ⟨x, Run.skip x, hx, Below.refl _ _⟩
  | atom a s => exact ⟨_, Run.atom _ x, by rw [view_atom, hx], below_atom _ _ _ _⟩
  | seq h₁ h₂ ih₁ ih₂ =>
    obtain ⟨u, hu, hv, hlow⟩ := ih₁ x hx
    obtain ⟨y, hy, hw, hwlow⟩ := ih₂ u hv
    exact ⟨y, Run.seq hu hy, hw, hlow.trans hwlow⟩
  | branchTrue hg hr ih =>
    obtain ⟨y, hy, hv, hb⟩ := ih x hx
    exact ⟨y, Run.branchTrue (by rw [guard_view, hx]; exact hg) hy, hv, hb⟩
  | branchFalse hg hr ih =>
    obtain ⟨y, hy, hv, hb⟩ := ih x hx
    exact ⟨y, Run.branchFalse (by rw [guard_view, hx]; exact hg) hy, hv, hb⟩
  | loopFalse hg => exact ⟨x, Run.loopFalse (by rw [guard_view, hx]; exact hg), hx, Below.refl _ _⟩
  | loopTrue hg h₁ h₂ ih₁ ih₂ =>
    obtain ⟨u, hu, hv, hlow⟩ := ih₁ x hx
    obtain ⟨y, hy, hw, hwlow⟩ := ih₂ u hv
    exact ⟨y, Run.loopTrue (by rw [guard_view, hx]; exact hg) hu hy, hw, hlow.trans hwlow⟩

end NearLinearRSP.TwoResources.Supplement.RegisterShift

end

section

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000

namespace NearLinearRSP.TwoResources.Supplement
open Mission.Structured

def WorkRegister (d a : ℕ) : Prop := a = 0 ∨ 8 ≤ a ∧ a < 8 + 8 * d

structure RegisterFrame (d : ℕ) (s t : Store) : Prop where
  nr : ∀ a, ¬WorkRegister d a → t.nr a = s.nr a
  rr : ∀ a, ¬WorkRegister d a → t.rr a = s.rr a
  nm : t.nm = s.nm
  rm : t.rm = s.rm

theorem RegisterFrame.refl (d : ℕ) (s : Store) : RegisterFrame d s s :=
  ⟨fun _ _ => rfl, fun _ _ => rfl, rfl, rfl⟩

theorem RegisterFrame.trans {d : ℕ} {s t u : Store}
    (h : RegisterFrame d s t) (g : RegisterFrame d t u) : RegisterFrame d s u :=
  ⟨fun a ha => (g.nr a ha).trans (h.nr a ha),
    fun a ha => (g.rr a ha).trans (h.rr a ha), g.nm.trans h.nm, g.rm.trans h.rm⟩

theorem RegisterFrame.mono {d e : ℕ} {s t : Store} (h : RegisterFrame d s t) (hde : d ≤ e) :
    RegisterFrame e s t := by
  have hw : ∀ a, WorkRegister d a → WorkRegister e a := by
    intro a ha; unfold WorkRegister at *; omega
  exact ⟨fun a ha => h.nr a (fun hh => ha (hw a hh)),
    fun a ha => h.rr a (fun hh => ha (hw a hh)), h.nm, h.rm⟩

theorem RegisterFrame.small_nr {d : ℕ} {s t : Store} (h : RegisterFrame d s t)
    (a : ℕ) (ha : 0 < a) (ha8 : a < 8) : t.nr a = s.nr a :=
  h.nr a (by unfold WorkRegister; omega)

theorem RegisterFrame.small_rr {d : ℕ} {s t : Store} (h : RegisterFrame d s t)
    (a : ℕ) (ha : 0 < a) (ha8 : a < 8) : t.rr a = s.rr a :=
  h.rr a (by unfold WorkRegister; omega)

theorem RegisterFrame.large_nr {d : ℕ} {s t : Store} (h : RegisterFrame d s t)
    (a : ℕ) (ha : 8 + 8 * d ≤ a) : t.nr a = s.nr a :=
  h.nr a (by unfold WorkRegister; omega)

theorem RegisterFrame.large_rr {d : ℕ} {s t : Store} (h : RegisterFrame d s t)
    (a : ℕ) (ha : 8 + 8 * d ≤ a) : t.rr a = s.rr a :=
  h.rr a (by unfold WorkRegister; omega)

def SafeAtom (d : ℕ) : RAMInstr → Prop
  | .realConst a _ | .natConst a _ | .realCopy a _ | .natCopy a _ |
    .realOp _ a _ _ | .natOp _ a _ _ | .exp a _ |
    .loadReal a _ | .loadNat a _ | .inputReal a _ | .inputNat a _ => WorkRegister d a
  | _ => False

def SafeCmd (d : ℕ) : Cmd → Prop
  | .skip => True
  | .atom a => SafeAtom d a.val
  | .seq a b | .branch _ a b => SafeCmd d a ∧ SafeCmd d b
  | .loop _ body => SafeCmd d body

theorem update_nr_frame (d : ℕ) (s : Store) (a v : ℕ) (ha : WorkRegister d a) :
    RegisterFrame d s { s with nr := Function.update s.nr a v } := by
  refine ⟨?_, fun _ _ => rfl, rfl, rfl⟩
  intro b hb
  have hba : b ≠ a := fun he => hb (he.symm ▸ ha)
  exact Function.update_of_ne hba _ _

theorem update_rr_frame (d : ℕ) (s : Store) (a : ℕ) (v : ℝ) (ha : WorkRegister d a) :
    RegisterFrame d s { s with rr := Function.update s.rr a v } := by
  refine ⟨fun _ _ => rfl, ?_, rfl, rfl⟩
  intro b hb
  have hba : b ≠ a := fun he => hb (he.symm ▸ ha)
  exact Function.update_of_ne hba _ _

theorem safe_atom_frame (d : ℕ) (input : RAMInput) (s : Store) (a : Atom)
    (ha : SafeAtom d a.val) : RegisterFrame d s (a.eval input s) := by
  rcases a with ⟨a, hatom⟩
  cases a <;> simp only [SafeAtom] at ha
  all_goals first
    | exact ha.elim
    | exact update_nr_frame d s _ _ ha
    | exact update_rr_frame d s _ _ ha

theorem safe_run_frame {d : ℕ} {input : RAMInput} {c : Cmd} {s t : Store} {n : ℕ}
    (h : Run input c s t n) (hsafe : SafeCmd d c) : RegisterFrame d s t := by
  induction h with
  | skip s => exact RegisterFrame.refl d s
  | atom a s => exact safe_atom_frame d input s a hsafe
  | seq h₁ h₂ ih₁ ih₂ => exact (ih₁ hsafe.1).trans (ih₂ hsafe.2)
  | branchTrue hg hr ih => exact ih hsafe.1
  | branchFalse hg hr ih => exact ih hsafe.2
  | loopFalse hg => exact RegisterFrame.refl d _
  | loopTrue hg h₁ h₂ ih₁ ih₂ => exact (ih₁ hsafe).trans (ih₂ hsafe)

theorem SafeCmd.mono {d e : ℕ} {c : Cmd} (h : SafeCmd d c) (hde : d ≤ e) : SafeCmd e c := by
  have ha : ∀ a, SafeAtom d a → SafeAtom e a := by
    intro a hh
    cases a <;> simp only [SafeAtom, WorkRegister] at * <;> omega
  induction c with
  | skip => trivial
  | atom a => exact ha a.val h
  | seq a b iha ihb => exact ⟨iha h.1, ihb h.2⟩
  | branch g a b iha ihb => exact ⟨iha h.1, ihb h.2⟩
  | loop g body ih => exact ih h

end NearLinearRSP.TwoResources.Supplement

end

section

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
open scoped BigOperators

namespace NearLinearRSP.TwoResources.Supplement.TensorRAM
open Mission.Structured
open ActuarialValuation

theorem slot_work (n a : ℕ) (ha : a < 8) : WorkRegister (n + 1) (slot n a) := by
  unfold WorkRegister slot; omega

@[simp] theorem slot_ne_small (n a b : ℕ) (hb : b < 8) : slot n a ≠ b := by
  unfold slot; omega

@[simp] theorem small_ne_slot (n a b : ℕ) (hb : b < 8) : b ≠ slot n a :=
  (slot_ne_small n a b hb).symm

@[simp] theorem slot_eq_slot (n a b : ℕ) : slot n a = slot n b ↔ a = b := by
  unfold slot; omega

noncomputable def tensorValue (nm : ℕ → ℕ) (rm : ℕ → ℝ) (params : ℕ) : ℕ → ℕ → ℝ
  | 0, addr => rm addr
  | n + 1, addr =>
    ∑ j ∈ Finset.range (nm (params + 2 * n)),
      poissonCountMass (rm (params + 2 * n)) j *
        tensorValue nm rm params n (addr + j * nm (params + 2 * n + 1))

def tensorCost (q : ℕ) : ℕ → ℕ
  | 0 => 1
  | n + 1 => 13 + q * (tensorCost q n + 11)

theorem init_safe (n : ℕ) : SafeCmd (n + 1) (Cmd.atoms (init n)) := by
  simp only [init, Cmd.atoms, SafeCmd, SafeAtom, WorkRegister, slot]
  repeat' apply And.intro
  all_goals first | trivial | omega

theorem finish_safe (n : ℕ) : SafeCmd (n + 1) (Cmd.atoms (finish n)) := by
  simp only [finish, Cmd.atoms, SafeCmd, SafeAtom, WorkRegister, slot]
  repeat' apply And.intro
  all_goals first | trivial | exact Or.inl trivial | omega

theorem tensor_safe (n : ℕ) : SafeCmd n (tensorCmd n) := by
  induction n with
  | zero => exact Or.inl rfl
  | succ n ih =>
    exact ⟨init_safe n, ⟨⟨slot_work n 3 (by decide), ⟨ih.mono (by omega), finish_safe n⟩⟩,
      Or.inl rfl⟩⟩

theorem tensor_frame {n : ℕ} {input : RAMInput} {s t : Store} {steps : ℕ}
    (h : Run input (tensorCmd n) s t steps) : RegisterFrame n s t :=
  safe_run_frame h (tensor_safe n)

theorem mass_zero (μ : ℝ) : poissonCountMass μ 0 = Real.exp (-μ) := by
  simp [poissonCountMass]

theorem mass_succ (μ : ℝ) (j : ℕ) :
    poissonCountMass μ j * μ / ((j : ℝ) + 1) = poissonCountMass μ (j + 1) := by
  simp only [poissonCountMass, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one, pow_succ]
  have hj : (j : ℝ) + 1 ≠ 0 := by positivity
  have hf : (j.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero j
  field_simp

theorem init_fields (n : ℕ) (input : RAMInput) (s : Store)
    (hone : s.nr 2 = 1) (hzero : s.rr 2 = 0) :
    let t := evalAtoms input (init n) s
    t.nr 0 = s.nr 0 ∧ t.nr (slot n 0) = s.nm (s.nr 1 + 2 * n) ∧
      t.nr (slot n 1) = s.nm (s.nr 1 + 2 * n + 1) ∧ t.nr (slot n 2) = 0 ∧
      t.rr (slot n 0) = s.rm (s.nr 1 + 2 * n) ∧
      t.rr (slot n 1) = poissonCountMass (s.rm (s.nr 1 + 2 * n)) 0 ∧
      t.rr (slot n 2) = 0 ∧ t.rr (slot n 3) = 0 := by
  simp [init, evalAtoms, Atom.eval, Store.ofRAM, ramStep, Store.at, evalNat, evalReal,
    Function.update_apply, hone, hzero, mass_zero]

theorem save_fields (n : ℕ) (input : RAMInput) (s : Store) :
    let t := (save n).eval input s
    t.nr 0 = s.nr 0 ∧ t.nr (slot n 3) = s.nr 0 ∧
      (∀ a, a ≠ slot n 3 → t.nr a = s.nr a) ∧ t.rr = s.rr ∧ t.nm = s.nm ∧ t.rm = s.rm := by
  simp +contextual [save, Atom.eval, Store.ofRAM, ramStep, Store.at, Function.update_apply]

theorem finish_fields (n : ℕ) (input : RAMInput) (s : Store)
    (hone : s.nr 2 = 1) (hrone : s.rr 1 = 1) :
    let t := evalAtoms input (finish n) s
    t.nr 0 = s.nr (slot n 3) + s.nr (slot n 1) ∧
      t.nr (slot n 0) = s.nr (slot n 0) ∧ t.nr (slot n 1) = s.nr (slot n 1) ∧
      t.nr (slot n 2) = s.nr (slot n 2) + 1 ∧ t.rr (slot n 0) = s.rr (slot n 0) ∧
      t.rr (slot n 1) = s.rr (slot n 1) * s.rr (slot n 0) / (s.rr (slot n 2) + 1) ∧
      t.rr (slot n 2) = s.rr (slot n 2) + 1 ∧
      t.rr (slot n 3) = s.rr (slot n 3) + s.rr (slot n 1) * s.rr 0 := by
  simp [finish, evalAtoms, Atom.eval, Store.ofRAM, ramStep, Store.at, evalNat, evalReal,
    Function.update_apply, hone, hrone]

end NearLinearRSP.TwoResources.Supplement.TensorRAM

end

section

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
open scoped BigOperators

namespace NearLinearRSP.TwoResources.Supplement.TensorRAM
open Mission.Structured
open ActuarialValuation

structure LoopInv (n : ℕ) (s : Store) (j : ℕ) (t : Store) : Prop where
  frame : RegisterFrame (n + 1) s t
  addr : t.nr 0 = s.nr 0 + j * s.nm (s.nr 1 + 2 * n + 1)
  limit : t.nr (slot n 0) = s.nm (s.nr 1 + 2 * n)
  stride : t.nr (slot n 1) = s.nm (s.nr 1 + 2 * n + 1)
  counter : t.nr (slot n 2) = j
  mean : t.rr (slot n 0) = s.rm (s.nr 1 + 2 * n)
  mass : t.rr (slot n 1) = poissonCountMass (s.rm (s.nr 1 + 2 * n)) j
  realCounter : t.rr (slot n 2) = j
  sum : t.rr (slot n 3) = ∑ a ∈ Finset.range j,
    poissonCountMass (s.rm (s.nr 1 + 2 * n)) a *
      tensorValue s.nm s.rm (s.nr 1) n (s.nr 0 + a * s.nm (s.nr 1 + 2 * n + 1))

theorem init_inv (n : ℕ) (input : RAMInput) (s : Store)
    (hone : s.nr 2 = 1) (hzero : s.rr 2 = 0) :
    LoopInv n s 0 (evalAtoms input (init n) s) := by
  obtain ⟨ha, hl, hs, hc, hm, hp, hr, hz⟩ := init_fields n input s hone hzero
  exact ⟨safe_run_frame (run_atoms input (init n) s) (init_safe n), by simpa using ha,
    hl, hs, hc, hm, hp, by simpa using hr, by simpa using hz⟩

theorem tensor_run (n : ℕ) (input : RAMInput) (s : Store) (q : ℕ)
    (hone : s.nr 2 = 1) (hrone : s.rr 1 = 1) (hzero : s.rr 2 = 0)
    (hlimits : ∀ a < n, s.nm (s.nr 1 + 2 * a) ≤ q) :
    ∃ t steps, Run input (tensorCmd n) s t steps ∧
      t.rr 0 = tensorValue s.nm s.rm (s.nr 1) n (s.nr 0) ∧ steps ≤ tensorCost q n := by
  induction n generalizing s with
  | zero =>
    let a : Atom := ⟨.loadReal 0 0, trivial⟩
    refine ⟨a.eval input s, 1, Run.atom a s, ?_, le_refl _⟩
    simp [a, Atom.eval, Store.ofRAM, ramStep, Store.at, tensorValue]
  | succ n ih =>
    let lim := s.nm (s.nr 1 + 2 * n)
    let body := Cmd.seq (.atom (save n)) (.seq (tensorCmd n) (Cmd.atoms (finish n)))
    have hguard : ∀ j t, j ≤ lim → LoopInv n s j t →
        (Guard.nat .lt (slot n 2) (slot n 0)).eval t = decide (j < lim) := by
      intro j t _ h
      simp only [Guard.eval, natTest, h.counter, h.limit, lim]
    have hbody : ∀ j t, j < lim → LoopInv n s j t →
        ∃ out steps, Run input body t out steps ∧ LoopInv n s (j + 1) out ∧
          steps ≤ tensorCost q n + 9 := by
      intro j t hj h
      let v := (save n).eval input t
      have hv := save_fields n input t
      have hvframe : RegisterFrame (n + 1) s v :=
        h.frame.trans (safe_atom_frame (n + 1) input t (save n) (slot_work n 3 (by decide)))
      have hvparams : v.nr 1 = s.nr 1 := hvframe.small_nr 1 (by decide) (by decide)
      have hvone : v.nr 2 = 1 := (hvframe.small_nr 2 (by decide) (by decide)).trans hone
      have hvrone : v.rr 1 = 1 := (hvframe.small_rr 1 (by decide) (by decide)).trans hrone
      have hvzero : v.rr 2 = 0 := (hvframe.small_rr 2 (by decide) (by decide)).trans hzero
      have hvlimits : ∀ a < n, v.nm (v.nr 1 + 2 * a) ≤ q := by
        intro a ha
        rw [hvparams, hvframe.nm]
        exact hlimits a (by omega)
      obtain ⟨w, steps, hchild, hwval, hwcost⟩ := ih v hvone hvrone hvzero hvlimits
      have hwframe := tensor_frame hchild
      have hwnr (a : ℕ) : w.nr (slot n a) = v.nr (slot n a) :=
        hwframe.large_nr _ (by unfold slot; omega)
      have hwrr (a : ℕ) : w.rr (slot n a) = t.rr (slot n a) :=
        (hwframe.large_rr _ (by unfold slot; omega)).trans (congrFun hv.2.2.2.1 _)
      have hwnr' (a : ℕ) (ha : a ≠ 3) : w.nr (slot n a) = t.nr (slot n a) :=
        (hwnr a).trans (hv.2.2.1 _ (fun he => ha ((slot_eq_slot n a 3).mp he)))
      have hwsaved : w.nr (slot n 3) = s.nr 0 + j * s.nm (s.nr 1 + 2 * n + 1) :=
        (hwnr 3).trans (hv.2.1.trans h.addr)
      have hwvalue : w.rr 0 = tensorValue s.nm s.rm (s.nr 1) n
          (s.nr 0 + j * s.nm (s.nr 1 + 2 * n + 1)) := by
        rw [hwval, hvframe.nm, hvframe.rm, hvparams, hv.1, h.addr]
      have hwone : w.nr 2 = 1 := (hwframe.small_nr 2 (by decide) (by decide)).trans hvone
      have hwrone : w.rr 1 = 1 := (hwframe.small_rr 1 (by decide) (by decide)).trans hvrone
      let out := evalAtoms input (finish n) w
      obtain ⟨ha, hl, hs, hc, hm, hp, hr, hsum⟩ := finish_fields n input w hwone hwrone
      have houtframe : RegisterFrame (n + 1) s out :=
        (hvframe.trans (hwframe.mono (by omega))).trans
          (safe_run_frame (run_atoms input (finish n) w) (finish_safe n))
      have hout : LoopInv n s (j + 1) out := by
        refine ⟨houtframe, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · rw [ha, hwsaved, hwnr' 1 (by decide), h.stride]
          simp only [Nat.add_mul, Nat.one_mul, Nat.add_assoc]
        · exact hl.trans ((hwnr' 0 (by decide)).trans h.limit)
        · exact hs.trans ((hwnr' 1 (by decide)).trans h.stride)
        · rw [hc, hwnr' 2 (by decide), h.counter]
        · exact hm.trans ((hwrr 0).trans h.mean)
        · rw [hp, hwrr 1, hwrr 0, hwrr 2, h.mass, h.mean, h.realCounter]
          exact mass_succ _ _
        · rw [hr, hwrr 2, h.realCounter, Nat.cast_add, Nat.cast_one]
        · rw [hsum, hwrr 3, hwrr 1, h.sum, h.mass, hwvalue, Finset.sum_range_succ]
      refine ⟨out, 1 + (steps + (finish n).length),
        Run.seq (Run.atom (save n) t) (Run.seq hchild (run_atoms input (finish n) w)), hout, ?_⟩
      simp only [finish, List.length_cons, List.length_nil]
      omega
    obtain ⟨t, steps, hloop, hinv, hcost⟩ := run_bounded_loop input
      (.nat .lt (slot n 2) (slot n 0)) body lim (tensorCost q n + 9) (LoopInv n s)
      hguard hbody 0 (evalAtoms input (init n) s) (by omega) (init_inv n input s hone hzero)
    let final : Atom := ⟨.realCopy 0 (slot n 3), trivial⟩
    refine ⟨final.eval input t, (init n).length + (steps + 1),
      Run.seq (run_atoms input (init n) s) (Run.seq hloop (Run.atom final t)), ?_, ?_⟩
    · simpa [final, Atom.eval, Store.ofRAM, ramStep, Store.at, tensorValue, lim] using hinv.sum
    · have hlim : lim ≤ q := hlimits n (by omega)
      have hmul := Nat.mul_le_mul_left (tensorCost q n + 11) hlim
      simp only [Nat.sub_zero] at hcost
      simp only [init, List.length_cons, List.length_nil, tensorCost]
      nlinarith

end NearLinearRSP.TwoResources.Supplement.TensorRAM

end

section

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
open scoped BigOperators

namespace NearLinearRSP.TwoResources.Supplement.TensorRAM
open Mission.Structured
open ActuarialValuation

def box (bounds : ℕ → ℕ) : (d : ℕ) → List (Fin d → ℕ)
  | 0 => [fun r => Fin.elim0 r]
  | n + 1 => (List.range (bounds n)).flatMap
      (fun j => (box bounds n).map (fun a => Fin.snoc a j))

theorem box_mem (bounds : ℕ → ℕ) (d : ℕ) (a : Fin d → ℕ) :
    a ∈ box bounds d ↔ ∀ r, a r < bounds r.val := by
  induction d with
  | zero =>
    have ha : a = fun r => Fin.elim0 r := Subsingleton.elim _ _
    simp [box, ha]
  | succ n ih =>
    constructor
    · intro h
      obtain ⟨j, hj, hm⟩ := List.mem_flatMap.mp h
      obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hm
      intro r
      refine Fin.lastCases ?_ (fun s => ?_) r
      · simpa using List.mem_range.mp hj
      · simpa using (ih b).mp hb s
    · intro h
      apply List.mem_flatMap.mpr
      refine ⟨a (Fin.last n), List.mem_range.mpr (h (Fin.last n)), ?_⟩
      apply List.mem_map.mpr
      refine ⟨Fin.init a, (ih _).mpr (fun r => h r.castSucc), ?_⟩
      exact Fin.snoc_init_self a

theorem box_nodup (bounds : ℕ → ℕ) (d : ℕ) : (box bounds d).Nodup := by
  induction d with
  | zero => simp [box]
  | succ n ih =>
    rw [box, List.nodup_flatMap]
    constructor
    · intro j _
      exact ih.map (fun _ _ he => (Fin.snoc_inj.mp he).1)
    · apply (List.nodup_range (n := bounds n)).imp
      intro a b hab c hc hd
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hc
      obtain ⟨y, hy, he⟩ := List.mem_map.mp hd
      exact hab (Fin.snoc_inj.mp he).2.symm

theorem tensorValue_box (nm : ℕ → ℕ) (rm : ℕ → ℝ) (params d addr : ℕ) :
    tensorValue nm rm params d addr =
      ((box (fun r => nm (params + 2 * r)) d).map (fun a =>
        (∏ r : Fin d, poissonCountMass (rm (params + 2 * r.val)) (a r)) *
          rm (addr + ∑ r : Fin d, a r * nm (params + 2 * r.val + 1)))).sum := by
  induction d generalizing addr with
  | zero => simp [tensorValue, box]
  | succ n ih =>
    rw [tensorValue, box]
    simp only [List.flatMap_def, List.map_flatten, List.sum_flatten, List.map_map, Function.comp_def]
    rw [← List.sum_toFinset _ (List.nodup_range (n := nm (params + 2 * n)))]
    simp only [List.toFinset_range]
    apply Finset.sum_congr rfl
    intro j hj
    rw [ih, ← List.sum_map_mul_left]
    apply congrArg List.sum
    apply List.map_congr_left
    intro a ha
    simp only [Fin.prod_univ_castSucc, Fin.sum_univ_castSucc, Fin.snoc_castSucc,
      Fin.snoc_last, Fin.val_last, Fin.val_castSucc]
    rw [show addr + j * nm (params + 2 * n + 1) +
        ∑ r : Fin n, a r * nm (params + 2 * r.val + 1) =
        addr + ((∑ r : Fin n, a r * nm (params + 2 * r.val + 1)) +
          j * nm (params + 2 * n + 1)) by omega]
    ring

theorem box_perm_rectangle {k : ℕ} (A : ClockCall k) (i : Fin A.d → ℕ)
    (bounds : ℕ → ℕ) (hb : ∀ r : Fin A.d, bounds r.val = A.q - i r) :
    (box bounds A.d).Perm (rectangle A i) := by
  apply (List.perm_ext_iff_of_nodup (box_nodup bounds A.d) (rectangle_nodup A i)).mpr
  intro a
  rw [box_mem, rectangle_mem]
  constructor
  · intro ha r
    have hh := ha r
    rw [hb r] at hh
    omega
  · intro ha r
    rw [hb r]
    have hh := ha r
    omega

theorem tensorValue_expectation {k : ℕ} (A : ClockCall k) (T : MultiTable A.d)
    (u v : ℕ) (i : Fin A.d → ℕ) (nm : ℕ → ℕ) (rm : ℕ → ℝ) (params addr : ℕ)
    (hb : ∀ r : Fin A.d, nm (params + 2 * r.val) = A.q - i r)
    (hμ : ∀ r : Fin A.d, rm (params + 2 * r.val) = clockMean A r u v)
    (hmem : ∀ a ∈ rectangle A i,
      rm (addr + ∑ r : Fin A.d, a r * nm (params + 2 * r.val + 1)) =
        1 - value A T u (fun r => i r + a r)) :
    expectation A T u v i = 1 - tensorValue nm rm params A.d addr := by
  rw [tensorValue_box]
  rw [(box_perm_rectangle A i (fun r => nm (params + 2 * r)) hb).map _ |>.sum_eq]
  have he : ((rectangle A i).map (fun a =>
      (∏ r : Fin A.d, poissonCountMass (rm (params + 2 * r.val)) (a r)) *
        rm (addr + ∑ r : Fin A.d, a r * nm (params + 2 * r.val + 1)))).sum =
      ((rectangle A i).map (fun a => incrementMass A u v a *
        (1 - value A T u (fun r => i r + a r)))).sum := by
    apply congrArg List.sum
    apply List.map_congr_left
    intro a ha
    rw [hmem a ha]
    congr 1
    unfold incrementMass
    apply Finset.prod_congr rfl
    intro r _
    rw [hμ r]
  rw [he]
  have hsub {α : Type} (xs : List α) (f g : α → ℝ) :
      (xs.map (fun a => f a - g a)).sum = (xs.map f).sum - (xs.map g).sum := by
    induction xs with
    | nil => simp
    | cons a xs ih => simp only [List.map_cons, List.sum_cons, ih]; ring
  simp only [expectation, mul_sub, mul_one, hsub]
  ring

theorem tensorCost_bound (q d : ℕ) : tensorCost q d ≤ 25 ^ (d + 1) * (q + 1) ^ d := by
  induction d with
  | zero => norm_num [tensorCost]
  | succ d ih =>
    have hB : 1 ≤ 25 ^ (d + 1) * (q + 1) ^ d := Nat.one_le_iff_ne_zero.mpr (by positivity)
    have hmul := Nat.mul_le_mul_left q ih
    have hpow : 25 ^ (d + 1 + 1) * (q + 1) ^ (d + 1) =
        25 * (25 ^ (d + 1) * (q + 1) ^ d) * (q + 1) := by
      rw [pow_succ, pow_succ (q + 1)]
      ring
    rw [tensorCost, hpow]
    nlinarith

end NearLinearRSP.TwoResources.Supplement.TensorRAM

end

section

set_option autoImplicit false
set_option maxHeartbeats 1400000

namespace NearLinearRSP.TwoResources.Supplement.EdgeRAM
open Mission.Structured

theorem tensor_input (b : ℕ) (hb : 2 ≤ b) (input : RAMInput) (s : Store) :
    let p := evalAtoms input (tensorArgs b) s
    let v := RegisterShift.view b p
    v.nr 0 = s.nr 0 ∧ v.nr 1 = s.nr 1 ∧ v.nr 2 = 1 ∧ v.rr 1 = 1 ∧ v.rr 2 = 0 ∧
      v.nm = s.nm ∧ v.rm = s.rm ∧ RegisterShift.Below b s p := by
  dsimp only
  refine ⟨?_, ?_, ?_, ?_, ?_, rfl, rfl, ⟨?_, ?_⟩⟩
  all_goals first
    | intro a ha
      simp [tensorArgs, evalAtoms, Atom.eval, Store.ofRAM, Store.at, ramStep,
        Function.update_of_ne (show a ≠ b by omega), Function.update_of_ne (show a ≠ b + 1 by omega),
        Function.update_of_ne (show a ≠ b + 2 by omega)]
    | simp [RegisterShift.view, tensorArgs, evalAtoms, Atom.eval, Store.ofRAM, Store.at, ramStep,
        Function.update_of_ne (show 1 ≠ b by omega), Function.update_of_ne (show b ≠ b + 1 by omega),
        Function.update_of_ne (show b ≠ b + 2 by omega), Function.update_of_ne (show b + 1 ≠ b + 2 by omega)]

theorem kernel_run (k d q : ℕ) (input : RAMInput) (s : Store)
    (hb : ∀ j < d, s.nm (s.nr 1 + 2 * j) ≤ q) :
    ∃ t n, Run input (kernel k d) s t n ∧
      t.rr 88 = 1 - TensorRAM.tensorValue s.nm s.rm (s.nr 1) d (s.nr 0) ∧ t.nm = s.nm ∧ t.rm = s.rm ∧
      (∀ j < bank k, t.nr j = s.nr j) ∧ (∀ j < bank k, j ≠ 88 → t.rr j = s.rr j) ∧
      n ≤ TensorRAM.tensorCost q d + 6 := by
  let b := bank k
  let p := evalAtoms input (tensorArgs b) s
  let v := RegisterShift.view b p
  obtain ⟨h0, h1, h2, hr1, hr2, hm, hrm, hlow⟩ := tensor_input b (by dsimp [b, bank]; omega) input s
  change v.nm = s.nm at hm
  change v.rm = s.rm at hrm
  change v.nr 0 = _ at h0
  change v.nr 1 = _ at h1
  obtain ⟨w, c, he, hw, hc⟩ := TensorRAM.tensor_run d input v q h2 hr1 hr2 (by
    intro j hj; change s.nm (v.nr 1 + 2 * j) ≤ q; rw [h1]; exact hb j hj)
  have hf := TensorRAM.tensor_frame he
  obtain ⟨x, hx, hv, hkeep⟩ := RegisterShift.transport he b p rfl
  have hx0 : x.rr b = TensorRAM.tensorValue s.nm s.rm (s.nr 1) d (s.nr 0) := by
    have hh := (congrArg (fun z : Store => z.rr 0) hv).trans hw
    simpa only [RegisterShift.view, Nat.add_zero, hm, hrm, h0, h1] using hh
  have hx1 : x.rr (b + 1) = 1 :=
    (congrArg (fun z : Store => z.rr 1) hv).trans ((hf.small_rr 1 (by decide) (by decide)).trans hr1)
  have hxnm : x.nm = s.nm := (congrArg Store.nm hv).trans (hf.nm.trans hm)
  have hxrm : x.rm = s.rm := (congrArg Store.rm hv).trans (hf.rm.trans hrm)
  have hl := hlow.trans hkeep
  refine ⟨_, 5 + (c + 1), Run.seq (run_atoms input (tensorArgs b) s) (Run.seq hx (Run.atom (resultOp b) x)), ?_,
    hxnm, hxrm, hl.nat, ?_, by omega⟩
  · simp [resultOp, Atom.eval, Store.ofRAM, Store.at, ramStep, evalReal, hx0, hx1]
  · intro j hj hj88
    simpa [resultOp, Atom.eval, Store.ofRAM, Store.at, ramStep, Function.update_of_ne hj88] using hl.real j hj

end NearLinearRSP.TwoResources.Supplement.EdgeRAM

end

section

set_option autoImplicit false
set_option maxHeartbeats 1800000

namespace NearLinearRSP.TwoResources.Supplement.EdgeRAM
open Mission.Structured

theorem moment_nat_frame (n a : ℕ) (ha : a < 76 ∨ 86 < a) : a ∉ (moments n).natWrites := by
  induction n with
  | zero => simp [moments, Cmd.natWrites]
  | succ n ih =>
    have h : a ∉ (momentLane n).natWrites := by
      simp [momentLane, laneRead, budgetCmd, momentOps, Cmd.atoms, Cmd.natWrites, Atom.natWrites]; omega
    simp [moments, Cmd.natWrites, h, ih]

theorem increments_address {k : ℕ} (A : ClockCall k) (base u : ℕ) (i a : Fin A.d → ℕ) :
    scanAddress base A.I.graph.n A.q u i + (∑ r : Fin A.d, a r * ((A.d + 4) * A.I.graph.n * A.q ^ (A.d - 1 - r.val))) =
      scanAddress base A.I.graph.n A.q u (fun r => i r + a r) := by
  rw [scanAddress_add, vectorIndex, Finset.sum_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro r _; ring

theorem edge_score_run {k : ℕ} (A : ClockCall k) (ε : ℝ) (T : MultiTable A.d) (edge params base : ℕ)
    (e : ℕ × ℕ) (he : A.I.graph.edges[edge]? = some e) (hu : e.1 < A.I.graph.n) (i : Fin A.d → ℕ)
    (s : Store) (h : Rates A edge params s) (hfree : TableQuery.extent A base ≤ params)
    (hq : s.nr 57 = A.q) (haddr : s.nr 0 = scanAddress base A.I.graph.n A.q e.1 i)
    (hstate : ∀ r : Fin A.d, s.nr (TableQuery.stateReg r.val) = i r)
    (hstride : ∀ r : Fin A.d, s.nr (TableQuery.strideReg r.val) = (A.d + 4) * A.I.graph.n * A.q ^ (A.d - 1 - r.val))
    (hcell : ∀ a ∈ rectangle A i, s.rm (scanAddress base A.I.graph.n A.q e.1 (fun r => i r + a r)) =
      1 - value A T e.1 (fun r => i r + a r)) :
    ∃ t n, Run (multiInput A.I ε) (scoreCmd k A.d) s t n ∧ t.rr 88 = expectation A T e.1 e.2 i ∧
      (∀ j : Fin A.d, t.rm (params + 2 * j.val + 1) = clockPGF A j e.1 e.2) ∧
      (∀ a, a < params ∨ params + 2 * A.d ≤ a → t.nm a = s.nm a ∧ t.rm a = s.rm a) ∧
      n ≤ 25 * A.d + 25 ^ (A.d + 1) * (A.q + 1) ^ A.d + 6 := by
  let input := multiInput A.I ε
  obtain ⟨p, m, hp, hpr, hmeans, hrf, hpn, hcm⟩ := moments_run A ε edge params e he A.d le_rfl s h
  obtain ⟨v, hv, _, hvr, hvregs, hdata, hnf⟩ := limits_run A.d input p
  have preg (a : ℕ) (ha : a < 76 ∨ 86 < a) := hp.nat_frame a (moment_nat_frame _ _ ha)
  have ptr := hpr.start
  have vp : v.nr 1 = params := (hvregs 1 (by decide) (by decide) (by decide)).trans ptr
  have va : v.nr 0 = scanAddress base A.I.graph.n A.q e.1 i :=
    (hvregs 0 (by decide) (by decide) (by decide)).trans ((preg 0 (by omega)).trans haddr)
  have pn57 := (preg 57 (by omega)).trans hq
  have lanes (j : Fin A.d) : v.nm (params + 2 * j.val) = A.q - i j ∧
      v.nm (params + 2 * j.val + 1) = (A.d + 4) * A.I.graph.n * A.q ^ (A.d - 1 - j.val) := by
    have hc := (preg (TableQuery.stateReg j.val) (by have := TableQuery.state_large j.val; omega)).trans (hstate j)
    have hs := (preg (TableQuery.strideReg j.val) (by have := TableQuery.stride_large j.val; omega)).trans (hstride j)
    simpa only [ptr, hc, hs, pn57] using hdata j.val j.isLt
  have hmean (j : Fin A.d) : v.rm (params + 2 * j.val) = clockMean A j e.1 e.2 := by
    rw [hvr]; exact (hmeans j j.isLt).1
  obtain ⟨t, c, ht, hval, htn, htr, _, _, hcc⟩ := kernel_run k A.d A.q input v
    (fun j hj => by rw [vp, (lanes ⟨j, hj⟩).1]; omega)
  have hresult := TensorRAM.tensorValue_expectation A T e.1 e.2 i v.nm v.rm params (v.nr 0) (fun r => (lanes r).1) hmean (by
    intro a ha
    rw [va]
    simp_rw [(fun r => (lanes r).2)]
    rw [increments_address]
    have hlt := TableQuery.scanAddress_inside A base e.1 hu (fun r => i r + a r) ((rectangle_mem A i a).mp ha) 0 (by omega)
    rw [hvr, hrf _ (Or.inl (by omega))]
    exact hcell a ha)
  refine ⟨t, m + (7 * A.d + c), Run.seq hp (Run.seq hv ht), ?_, ?_, ?_, ?_⟩
  · rw [hval, vp, hresult]
  · intro j; rw [htr, hvr]; exact (hmeans j j.isLt).2
  · intro a ha
    exact ⟨(congrFun htn _).trans ((hnf a (by simpa only [ptr] using ha)).trans (congrFun hpn a)),
      (congrFun htr _).trans ((congrFun hvr _).trans (hrf a ha))⟩
  · have hb := TensorRAM.tensorCost_bound A.q A.d
    omega

end NearLinearRSP.TwoResources.Supplement.EdgeRAM

end

section

set_option autoImplicit false
set_option maxHeartbeats 1500000

namespace NearLinearRSP.TwoResources.Supplement.EdgeRAM
open Mission.Structured

theorem shifted_writes (b a : ℕ) (ha : a < b) (c : Cmd) :
    a ∉ (RegisterShift.cmd b c).natWrites ∧ a ∉ (RegisterShift.cmd b c).realWrites := by
  induction c with
  | skip => simp [RegisterShift.cmd, Cmd.natWrites, Cmd.realWrites]
  | atom x =>
    rcases x with ⟨i, hi⟩
    cases i <;> simp [RegisterShift.cmd, RegisterShift.atom, RegisterShift.instr, Cmd.natWrites, Cmd.realWrites,
      Atom.natWrites, Atom.realWrites] <;> omega
  | seq c d hc hd => simp [RegisterShift.cmd, Cmd.natWrites, Cmd.realWrites, hc.1, hc.2, hd.1, hd.2]
  | branch g c d hc hd => simp [RegisterShift.cmd, Cmd.natWrites, Cmd.realWrites, hc.1, hc.2, hd.1, hd.2]
  | loop g c hc => exact hc

theorem kernel_preserves (k d a : ℕ) (ha : a < bank k) :
    a ∉ (kernel k d).natWrites ∧ (a ≠ 88 → a ∉ (kernel k d).realWrites) := by
  obtain ⟨hn, hr⟩ := shifted_writes (bank k) a ha (TensorRAM.tensorCmd d)
  simp [kernel, tensorArgs, resultOp, Cmd.atoms, Cmd.natWrites, Cmd.realWrites, Atom.natWrites, Atom.realWrites, hn, hr]
  omega

theorem moment_real_frame (n a : ℕ) (ha : a < 84 ∨ 87 < a) : a ∉ (moments n).realWrites := by
  induction n with
  | zero => simp [moments, Cmd.realWrites]
  | succ n ih =>
    have h : a ∉ (momentLane n).realWrites := by
      simp [momentLane, laneRead, budgetCmd, momentOps, Cmd.atoms, Cmd.realWrites, Atom.realWrites]; omega
    simp [moments, Cmd.realWrites, h, ih]

theorem limits_preserve (n a : ℕ) (ha : a < 84 ∨ 86 < a) :
    a ∉ (limits n).natWrites ∧ a ∉ (limits n).realWrites := by
  induction n with
  | zero => simp [limits, Cmd.natWrites, Cmd.realWrites]
  | succ n ih =>
    simp [limits, natOps, Cmd.atoms, Cmd.realWrites, Cmd.natWrites, Atom.realWrites, Atom.natWrites, ih.1, ih.2]
    omega

theorem copies_readonly (dst src n : ℕ) :
    (TableQuery.addCopies dst src n).writesNatMemory = false ∧
      (TableQuery.addCopies dst src n).writesRealMemory = false ∧ (TableQuery.addCopies dst src n).realWrites = ∅ := by
  induction n with
  | zero => exact ⟨rfl, rfl, rfl⟩
  | succ n ih => simp [TableQuery.addCopies, Cmd.writesNatMemory, Cmd.writesRealMemory, Cmd.realWrites,
      Atom.writesNatMemory, Atom.writesRealMemory, Atom.realWrites, ih.1, ih.2.1, ih.2.2]

theorem tests_readonly (rs : List ℕ) : (tests rs).writesNatMemory = false ∧ (tests rs).writesRealMemory = false := by
  induction rs with
  | nil => exact ⟨rfl, rfl⟩
  | cons r rs ih =>
    change (false || (tests rs).writesNatMemory) = false ∧ (false || (tests rs).writesRealMemory) = false
    simpa using ih

theorem load_memory {k n : ℕ} {input : RAMInput} {s t : Store} (h : Run input (loadEdge k) s t n) :
    t.nm = s.nm ∧ t.rm = s.rm := by
  obtain ⟨cn, cr, _⟩ := copies_readonly 70 75 k
  obtain ⟨tn, tr⟩ := tests_readonly (List.range (k - 1))
  refine ⟨h.natMemory_frame ?_, h.realMemory_frame ?_⟩
  · change ((false || ((TableQuery.addCopies 70 75 k).writesNatMemory || false)) || (false || (tests (List.range (k - 1))).writesNatMemory)) = false
    simp [cn, tn]
  · change ((false || ((TableQuery.addCopies 70 75 k).writesRealMemory || false)) || (false || (tests (List.range (k - 1))).writesRealMemory)) = false
    simp [cr, tr]

end NearLinearRSP.TwoResources.Supplement.EdgeRAM

end

section

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace NearLinearRSP.TwoResources.Supplement.LayerRAM
open Mission.Structured TableQuery

def StableNat (a : ℕ) : Prop := (30 ≤ a ∧ a < 49) ∨ (49 < a ∧ a < 70) ∨ a = 79 ∨ a = 93 ∨ (97 ≤ a ∧ a ≠ 100)

theorem moments_preserve (n a : ℕ) (h : a ≠ 76 ∧ a ≠ 84 ∧ a ≠ 85 ∧ a ≠ 86) : a ∉ (EdgeRAM.moments n).natWrites := by
  induction n with
  | zero => simp [EdgeRAM.moments, Cmd.natWrites]
  | succ n ih =>
    have hl : a ∉ (EdgeRAM.momentLane n).natWrites := by
      simp [EdgeRAM.momentLane, EdgeRAM.laneRead, EdgeRAM.budgetCmd, EdgeRAM.momentOps, Cmd.atoms, Cmd.natWrites, Atom.natWrites]
      omega
    simp [EdgeRAM.moments, Cmd.natWrites, ih, hl]

theorem evaluate_preserves (k d a : ℕ) (hf : a < EdgeRAM.bank k) :
    (StableNat a ∨ a = 95 ∨ a = 96 ∨ a = 100 → a ∉ (EdgeRAM.scoreCmd k d).natWrites) ∧
    (a < 84 ∨ 88 < a → a ∉ (EdgeRAM.scoreCmd k d).realWrites) := by
  obtain ⟨hn, hr⟩ := EdgeRAM.kernel_preserves k d a hf
  constructor
  · intro h
    simp only [StableNat] at h
    have hm := moments_preserve d a (by omega)
    have hl := (EdgeRAM.limits_preserve d a (by omega)).1
    simp [EdgeRAM.scoreCmd, Cmd.natWrites, hm, hl, hn]
  · intro h
    have hm := EdgeRAM.moment_real_frame d a (by omega)
    have hl := (EdgeRAM.limits_preserve d a (by omega)).2
    simp [EdgeRAM.scoreCmd, Cmd.realWrites, hm, hl, hr (by omega)]

theorem copy_registers (d a : ℕ) (h : a ≠ 85) (h' : a ≠ 87) :
    a ∉ (copyPGF d).natWrites ∧ a ∉ (copyPGF d).realWrites := by
  induction d with
  | zero => simp [copyPGF, Cmd.natWrites, Cmd.realWrites]
  | succ d ih =>
    simp [copyPGF, pgfOps, Cmd.atoms, Cmd.natWrites, Cmd.realWrites, Atom.natWrites, Atom.realWrites, ih.1, ih.2, h, h']

theorem compare_registers (d a : ℕ) :
    (StableNat a → a ∉ (compareEdge d).natWrites) ∧ (80 ≤ a → a ≤ 83 → a ∉ (compareEdge d).realWrites) := by
  have htree (r : ℕ) (hr : 30 ≤ r) : r ∉ updateCmd.natWrites ∧ r ∉ updateCmd.realWrites := by
    have hn : ∀ j ∈ updateCmd.natWrites, j < 30 := by decide
    have hrr : ∀ j ∈ updateCmd.realWrites, j < 30 := by decide
    exact ⟨fun h => (Nat.not_lt_of_ge hr) (hn _ h), fun h => (Nat.not_lt_of_ge hr) (hrr _ h)⟩
  constructor
  · intro hh
    unfold StableNat at hh
    have hc := copies_preserve 49 100 (d + 4) a (by omega)
    have hp := (copy_registers d a (by omega) (by omega)).1
    have ht := (htree a (by omega)).1
    simp [compareEdge, writeParent, parentStart, parentOps, Cmd.atoms, Cmd.natWrites, Atom.natWrites, hc, hp, ht]
    omega
  · intro h1 h2
    have hc := (EdgeRAM.copies_readonly 49 100 (d + 4)).2.2
    have hp := (copy_registers d a (by omega) (by omega)).2
    have ht := (htree a (by omega)).2
    simp [compareEdge, writeParent, parentStart, parentOps, Cmd.atoms, Cmd.realWrites, Atom.realWrites, hc, hp, ht]
    omega

theorem load_registers (k a : ℕ) :
    (StableNat a → a ∉ (EdgeRAM.loadEdge k).natWrites) ∧ (80 ≤ a → a ≤ 83 → a ∉ (EdgeRAM.loadEdge k).realWrites) := by
  constructor
  · intro hh
    unfold StableNat at hh
    have hc := copies_preserve 70 75 k a (by omega)
    have ht := EdgeRAM.tests_registers (List.range (k - 1)) a (by omega) (by omega)
    simp [EdgeRAM.loadEdge, EdgeRAM.readCmd, EdgeRAM.baseOps, EdgeRAM.lengthOp, EdgeRAM.restrictions, EdgeRAM.reject,
      Cmd.atoms, Cmd.natWrites, Atom.natWrites, hc, ht]
    omega
  · intro h1 h2
    have hc := (EdgeRAM.copies_readonly 70 75 k).2.2
    have ht := EdgeRAM.tests_real_registers (List.range (k - 1)) a (by omega) (by omega)
    simp [EdgeRAM.loadEdge, EdgeRAM.readCmd, EdgeRAM.baseOps, EdgeRAM.lengthOp, EdgeRAM.restrictions, EdgeRAM.reject,
      Cmd.atoms, Cmd.realWrites, Atom.realWrites, hc, ht]
    omega

theorem visit_registers (k d a : ℕ) (ha : a < EdgeRAM.bank k) :
    (StableNat a → a ∉ (visitEdge k d).natWrites) ∧ (80 ≤ a → a ≤ 83 → a ∉ (visitEdge k d).realWrites) := by
  obtain ⟨en, er⟩ := evaluate_preserves k d a ha
  obtain ⟨cn, cr⟩ := compare_registers d a
  obtain ⟨ln, lr⟩ := load_registers k a
  constructor
  · intro hh
    have hn := en (Or.inl hh)
    have ht := cn hh
    have hl := ln hh
    unfold StableNat at hh
    simp [visitEdge, scoreEdge, scoreArgs, probeLeaf, Cmd.atoms, Cmd.natWrites, Atom.natWrites, hn, ht, hl]
    omega
  · intro h1 h2
    have hr := er (Or.inl (by omega))
    have ht := cr h1 h2
    have hl := lr h1 h2
    simp [visitEdge, scoreEdge, scoreArgs, probeLeaf, Cmd.atoms, Cmd.realWrites, Atom.realWrites, hr, ht, hl]
    omega

end NearLinearRSP.TwoResources.Supplement.LayerRAM

end

section

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace NearLinearRSP.TwoResources.Supplement.LayerRAM
open Mission.Structured TableQuery

structure RegisterFrame (k : ℕ) (s t : Store) : Prop where
  nat : ∀ a, a < EdgeRAM.bank k → StableNat a → t.nr a = s.nr a
  real : ∀ a, 80 ≤ a → a ≤ 83 → t.rr a = s.rr a

theorem visiting_frame {k d n : ℕ} {input : RAMInput} {s t : Store} (h : Run input (visitEdge k d) s t n) :
    RegisterFrame k s t := by
  refine ⟨fun a ha hr => h.nat_frame a ((visit_registers k d a ha).1 hr), ?_⟩
  intro a h1 h2
  exact h.real_frame a ((visit_registers k d a (by unfold EdgeRAM.bank; omega)).2 h1 h2)

theorem loading_frame {k n : ℕ} {input : RAMInput} {s t : Store} (h : Run input (EdgeRAM.loadEdge k) s t n) :
    RegisterFrame k s t := ⟨fun a _ hr => h.nat_frame a ((load_registers k a).1 hr),
      fun a h1 h2 => h.real_frame a ((load_registers k a).2 h1 h2)⟩

theorem probing_frame (k : ℕ) (input : RAMInput) (s : Store) : RegisterFrame k s (evalAtoms input probeLeaf s) := by
  let h := run_atoms input probeLeaf s
  refine ⟨?_, ?_⟩
  · intro a _ hh
    apply h.nat_frame
    simp only [StableNat] at hh
    simp [probeLeaf, Cmd.atoms, Cmd.natWrites, Atom.natWrites]
    omega
  · intro a h1 h2
    apply h.real_frame
    simp [probeLeaf, Cmd.atoms, Cmd.realWrites, Atom.realWrites]
    omega

structure RowControl {k : ℕ} (A : ClockCall k) (base params B W P : ℕ) (i : Fin A.d → ℕ) (s : Store) : Prop where
  cfg : Config B W P s
  zero : s.nr 30 = 0
  q : s.nr 57 = A.q
  mode : s.nr 79 = if A.zeroOnly then 1 else 0
  row : s.nr 98 = rowCell A base i 0
  parameters : s.nr 190 = params
  counts : ∀ r : Fin A.d, s.nr (stateReg r.val) = i r
  strides : ∀ r : Fin A.d, s.nr (strideReg r.val) = stride A.I.graph.n A.q r
  limit : s.rr 80 = (A.q : ℝ)
  denom : s.rr 81 = 1 + A.δ / 2
  threshold : s.rr 82 = A.L
  decay : s.rr 83 = clockZ A - 1

def ControlNat (d a : ℕ) : Prop :=
  a ∈ [30, 57, 79, 98, 180, 181, 188, 190] ∨
    ∃ r < d, a = stateReg r ∨ a = strideReg r

theorem control_addresses {d a : ℕ} (h : ControlNat d a) :
    StableNat a ∧ a ≠ 75 ∧ a ≠ 86 ∧ a ≠ 191 ∧ a ≠ 194 ∧ 30 ≤ a ∧ a ≠ 95 ∧ a ≠ 96 ∧ a ≠ 97 ∧ a ≠ 99 ∧ a ≠ 93 ∧ a ≠ 94 ∧ a ≠ 92 := by
  simp only [ControlNat, List.mem_cons, List.not_mem_nil, or_false, stateReg, strideReg, CandidateRAM.current] at h
  unfold StableNat
  rcases h with h | ⟨r, hr, h⟩ <;> omega

theorem control_bank {k d a : ℕ} (hd : d ≤ k) (h : ControlNat d a) : a < EdgeRAM.bank k := by
  simp only [ControlNat, List.mem_cons, List.not_mem_nil, or_false, stateReg, strideReg, CandidateRAM.current] at h
  unfold EdgeRAM.bank
  rcases h with h | ⟨r, hr, h⟩ <;> omega

theorem RowControl.transfer {k : ℕ} {A : ClockCall k} {base params B W P : ℕ} {i : Fin A.d → ℕ}
    {s t : Store} (h : RowControl A base params B W P i s)
    (hn : ∀ a, ControlNat A.d a → t.nr a = s.nr a) (hr : ∀ a, 80 ≤ a → a ≤ 83 → t.rr a = s.rr a) :
    RowControl A base params B W P i t := by
  refine ⟨⟨(hn 180 (by simp [ControlNat])).trans h.cfg.winnerBase, (hn 181 (by simp [ControlNat])).trans h.cfg.parentBase,
    (hn 188 (by simp [ControlNat])).trans h.cfg.capacity⟩,
    (hn 30 (by simp [ControlNat])).trans h.zero, (hn 57 (by simp [ControlNat])).trans h.q,
    (hn 79 (by simp [ControlNat])).trans h.mode, (hn 98 (by simp [ControlNat])).trans h.row,
    (hn 190 (by simp [ControlNat])).trans h.parameters, ?_, ?_, (hr 80 (by decide) (by decide)).trans h.limit,
    (hr 81 (by decide) (by decide)).trans h.denom, (hr 82 (by decide) (by decide)).trans h.threshold,
    (hr 83 (by decide) (by decide)).trans h.decay⟩
  · intro r
    exact (hn _ (Or.inr ⟨r.val, r.isLt, Or.inl rfl⟩)).trans (h.counts r)
  · intro r
    exact (hn _ (Or.inr ⟨r.val, r.isLt, Or.inr rfl⟩)).trans (h.strides r)

structure EdgeContext {k : ℕ} (A : ClockCall k) (base params B W P u : ℕ) (i : Fin A.d → ℕ) (s : Store)
    extends RowControl A base params B W P i s : Prop where
  source : s.nr 97 = u
  address : s.nr 99 = rowCell A base i u

theorem EdgeContext.frame {k : ℕ} {A : ClockCall k} {base params B W P u : ℕ} {i : Fin A.d → ℕ}
    {s t : Store} (h : EdgeContext A base params B W P u i s) (hf : RegisterFrame k s t) :
    EdgeContext A base params B W P u i t := by
  have hc := h.toRowControl.transfer (fun a ha => hf.nat a (control_bank (clockCoordinates_length_le A.I) ha) (control_addresses ha).1) hf.real
  exact ⟨hc, (hf.nat 97 (by unfold EdgeRAM.bank; omega) (by norm_num [StableNat])).trans h.source,
    (hf.nat 99 (by unfold EdgeRAM.bank; omega) (by norm_num [StableNat])).trans h.address⟩

def GridValues {k : ℕ} (A : ClockCall k) (base u : ℕ) (i : Fin A.d → ℕ) (T : MultiTable A.d) (s : Store) : Prop :=
  ∀ a ∈ rectangle A i, s.rm (rowCell A base (fun r => i r + a r) u) = 1 - value A T u (fun r => i r + a r)

end NearLinearRSP.TwoResources.Supplement.LayerRAM

end

section

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace NearLinearRSP.TwoResources.Supplement.LayerRAM
open Mission.Structured TableQuery
open Mission.Queue (activeLeaf)

theorem scoring_frame {k d m : ℕ} {input : RAMInput} {s t : Store} (h : Run input (EdgeRAM.scoreCmd k d) s t m) :
    RegisterFrame k s t := by
  refine ⟨fun a ha hr => h.nat_frame a ((evaluate_preserves k d a ha).1 (Or.inl hr)), ?_⟩
  intro a h1 h2
  exact h.real_frame a ((evaluate_preserves k d a (by unfold EdgeRAM.bank; omega)).2 (Or.inl (by omega)))

theorem arguments_frame (k : ℕ) (input : RAMInput) (s : Store) : RegisterFrame k s (evalAtoms input scoreArgs s) := by
  refine ⟨?_, fun _ _ _ => rfl⟩
  intro a _ hr
  unfold StableNat at hr
  simp [scoreArgs, evalAtoms, Atom.eval, Store.at, Store.ofRAM, ramStep, Function.update_of_ne (show a ≠ 0 by omega),
    Function.update_of_ne (show a ≠ 1 by omega), Function.update_of_ne (show a ≠ 74 by omega)]

theorem score_edge_run {k : ℕ} (A : ClockCall k) (ε : ℝ) (base params B W P u v edge : ℕ) (i : Fin A.d → ℕ)
    (S : MultiLayer A.d) (s : Store) (he : A.I.graph.edges[edge]? = some (u,v)) (hv : v ∈ incidentVertices A.I)
    (hq : v ∈ S.queue) (hi : ∀ r, i r < A.q) (hB : (incidentVertices A.I).length ≤ B)
    (hsep : extent A base ≤ params) (hW : params + 2 * A.d ≤ W)
    (H : EdgeContext A base params B W P u i s)
    (heap : Heap B W P (activeLeaf (incidentVertices A.I) S.queue S.keys B) s)
    (parents : ParentRecords A base i S.parents s) (grid : GridValues A base u i S.table s)
    (coords : ∀ r : Fin A.d, s.nm (8 + r.val) = (A.coords.get r).val)
    (row : s.nr 70 = InputValues.row k edge) (hh : s.nr 100 = v)
    (hj : s.nr 95 = (incidentVertices A.I).idxOf v) (ht : s.nr 96 = (incidentVertices A.I).idxOf v + 1)
    (hk : s.rr 92 = S.keys v) :
    let U := offer u v (expectation A S.table u v i) S
    ∃ t n, Run (multiInput A.I ε) (scoreEdge k A.d) s t n ∧
      Heap B W P (activeLeaf (incidentVertices A.I) U.queue U.keys B) t ∧ ParentRecords A base i U.parents t ∧
      CompareFrame params (rowCell A base i v) A.d s t ∧
      n ≤ 32 * A.d + 25 ^ (A.d + 1) * (A.q + 1) ^ A.d + 19 * Nat.clog 2 (2 * B) + 35 := by
  let input := multiInput A.I ε
  let p := evalAtoms input scoreArgs s
  have hc := H.frame (arguments_frame k input s)
  have rates : EdgeRAM.Rates A edge params p :=
    ⟨H.parameters, row, rfl, H.limit, H.denom, H.threshold, H.decay, coords⟩
  have hu := (A.I.graph.endpoints (u,v) (List.mem_of_getElem? he)).1
  obtain ⟨w, n, hr, hscore, hpg, hf, hn⟩ := EdgeRAM.edge_score_run A ε S.table edge params base (u,v) he hu i p
    rates hsep hc.q H.address hc.counts hc.strides grid
  have hw := hc.frame (scoring_frame hr)
  have hbelow (x : ℕ) (hx : x < params) : w.nm x = s.nm x ∧ w.rm x = s.rm x := hf x (Or.inl hx)
  have habove (x : ℕ) (hx : W ≤ x) : w.nm x = s.nm x ∧ w.rm x = s.rm x := hf x (Or.inr (by omega))
  have hheap := heap.congr (fun j _ => habove _ (by omega)) (fun j _ => (habove _ (by have := heap.disjoint; omega)).1)
  have hpars := parents.congr hi (fun x hx => hbelow _ (by omega))
  have h95 := hr.nat_frame 95 ((evaluate_preserves k A.d 95 (by unfold EdgeRAM.bank; omega)).1 (by simp))
  have h96 := hr.nat_frame 96 ((evaluate_preserves k A.d 96 (by unfold EdgeRAM.bank; omega)).1 (by simp))
  have h100 := hr.nat_frame 100 ((evaluate_preserves k A.d 100 (by unfold EdgeRAM.bank; omega)).1 (by simp))
  have h92 := hr.real_frame 92 ((evaluate_preserves k A.d 92 (by unfold EdgeRAM.bank; omega)).2 (by omega))
  obtain ⟨t, c, hcmp, hqueue, hp, hframe, hcost⟩ := compare_edge_run A base params B W P u v i S
    (expectation A S.table u v i) input w hv hq hi hB hsep (by omega) hw.cfg hheap hpars hw.source
    (h100.trans hh) hw.row hw.parameters (h95.trans hj) (h96.trans ht) hscore (h92.trans hk) hpg
  refine ⟨t, 3 + (n+c), Run.seq (run_atoms input scoreArgs s) (Run.seq hr hcmp), hqueue, hp, ⟨?_, ?_⟩, by omega⟩
  · intro x hx h0 h1
    exact (hframe.nat x (by omega) h0 h1).trans (hbelow x hx).1
  · intro x hx hs
    exact (hframe.real x (by omega) hs).trans (hbelow x hx).2

end NearLinearRSP.TwoResources.Supplement.LayerRAM

end

section

set_option autoImplicit false
set_option maxHeartbeats 1800000

namespace NearLinearRSP.TwoResources.Supplement.LayerRAM
open Mission.Structured TableQuery
open Mission.Queue (activeLeaf)

theorem Heap.memory {B W P : ℕ} {leaf : ℕ → Mission.Queue.Record} {s t : Store}
    (h : Heap B W P leaf s) (hn : t.nm = s.nm) (hr : t.rm = s.rm) : Heap B W P leaf t :=
  h.congr (fun j _ => ⟨congrFun hn _, congrFun hr _⟩) (fun _ _ => congrFun hn _)

theorem CompareFrame.before {W a d : ℕ} {s p t : Store} (h : CompareFrame W a d p t)
    (hn : p.nm = s.nm) (hr : p.rm = s.rm) : CompareFrame W a d s t :=
  ⟨fun x hx h0 h1 => (h.nat x hx h0 h1).trans (congrFun hn x), fun x hx hs => (h.real x hx hs).trans (congrFun hr x)⟩

theorem visit_edge_run {k : ℕ} (A : ClockCall k) (hk : 0 < k) (ε : ℝ)
    (base params B W P u v edge : ℕ) (i : Fin A.d → ℕ) (S : MultiLayer A.d) (s : Store)
    (he : A.I.graph.edges[edge]? = some (u,v)) (hi : ∀ r, i r < A.q)
    (hB : (incidentVertices A.I).length ≤ B) (hsep : extent A base ≤ params) (hW : params + 2 * A.d ≤ W)
    (H : EdgeContext A base params B W P u i s) (h75 : s.nr 75 = edge)
    (heap : Heap B W P (activeLeaf (incidentVertices A.I) S.queue S.keys B) s)
    (parents : ParentRecords A base i S.parents s) (grid : GridValues A base u i S.table s)
    (coords : ∀ r : Fin A.d, s.nm (8 + r.val) = (A.coords.get r).val)
    (idx : s.nm (s.nr 141 + v) = (incidentVertices A.I).idxOf v + 1) :
    let U := guarded A i u S (u,v)
    ∃ t n, Run (multiInput A.I ε) (visitEdge k A.d) s t n ∧
      Heap B W P (activeLeaf (incidentVertices A.I) U.queue U.keys B) t ∧ ParentRecords A base i U.parents t ∧
      CompareFrame params (rowCell A base i v) A.d s t ∧ n ≤ visitCost k A.d A.q B := by
  dsimp only
  let input := multiInput A.I ε
  let xs := incidentVertices A.I
  have hv : v ∈ xs := activeVertices_edge_right (lengthInstance A.I) u v (List.mem_of_getElem? he)
  obtain ⟨p, m, hp, hflag, hrow, _, hhead, _, hm⟩ := EdgeRAM.edge_run A hk ε edge (u,v) he s h75 H.mode
  obtain ⟨hn, hr⟩ := EdgeRAM.load_memory hp
  have ph := H.frame (loading_frame hp)
  have pheap := heap.memory hn hr
  have pparents := parents.congr hi (fun _ _ => ⟨congrFun hn _, congrFun hr _⟩)
  by_cases hcall : (u,v) ∈ callEdges A
  · have hg : (Guard.nat .eq 71 30).eval p = false := by simp [Guard.eval, natTest, hflag, hcall, ph.zero]
    let b := evalAtoms input probeLeaf p
    have pidx : p.nm (p.nr 141 + v) = xs.idxOf v + 1 := by
      rw [hn, (loading_frame hp).nat 141 (by unfold EdgeRAM.bank; omega) (by norm_num [StableNat])]
      exact idx
    obtain ⟨bh, bj, bt, bk, bn, br⟩ := probe_leaf xs S.queue S.keys B W P v input p pheap ph.cfg hB hv hhead pidx
    change b.nr 96 = _ at bt
    have bnm : b.nm = s.nm := bn.trans hn
    have brm : b.rm = s.rm := br.trans hr
    have bH : EdgeContext A base params B W P u i b := ph.frame (probing_frame k input p)
    have bheap := heap.memory bnm brm
    have bpars := parents.congr hi (fun _ _ => ⟨congrFun bnm _, congrFun brm _⟩)
    have probeRun : Run input (.atoms probeLeaf) p b 9 := run_atoms input probeLeaf p
    by_cases hq : v ∈ S.queue
    · have ht : b.nr 96 = xs.idxOf v + 1 := by simpa only [if_pos hq] using bt
      have hqueued : (Guard.nat .eq 96 30).eval b = false := by simp [Guard.eval, natTest, ht, bH.zero]
      have bgrid : GridValues A base u i S.table b := fun a ha => (congrFun brm _).trans (grid a ha)
      obtain ⟨t, c, hs, hnew, hpar, hframe, hc⟩ := score_edge_run A ε base params B W P u v edge i S b he hv hq hi hB
        hsep hW bH bheap bpars bgrid (fun r => (congrFun bnm _).trans (coords r)) hrow bh bj ht bk
      have hU : guarded A i u S (u,v) = offer u v (expectation A S.table u v i) S := by
        simp [guarded, hcall, relax_as_offer, hq]
      rw [hU]
      exact ⟨t, _, Run.seq hp (Run.branchFalse hg (Run.seq probeRun (Run.branchFalse hqueued hs))),
        hnew, hpar, hframe.before bnm brm, by unfold visitCost; omega⟩
    · have hqueued : (Guard.nat .eq 96 30).eval b = true := by simp [Guard.eval, natTest, bt, hq, bH.zero]
      have hU : guarded A i u S (u,v) = S := by simp [guarded, hcall, relax_as_offer, hq]
      rw [hU]
      exact ⟨b, _, Run.seq hp (Run.branchFalse hg (Run.seq probeRun (Run.branchTrue hqueued (Run.skip b)))),
        bheap, bpars, ⟨fun _ _ _ _ => congrFun bnm _, fun _ _ _ => congrFun brm _⟩, by unfold visitCost; omega⟩
  · have hg : (Guard.nat .eq 71 30).eval p = true := by simp [Guard.eval, natTest, hflag, hcall, ph.zero]
    simp only [guarded, if_neg hcall]
    exact ⟨p, _, Run.seq hp (Run.branchTrue hg (Run.skip p)), pheap, pparents,
      ⟨fun _ _ _ _ => congrFun hn _, fun _ _ _ => congrFun hr _⟩, by unfold visitCost; omega⟩

end NearLinearRSP.TwoResources.Supplement.LayerRAM

end

section

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace NearLinearRSP.TwoResources.Supplement.LayerRAM
open Mission.Structured TableQuery

structure ScanMemory {k : ℕ} (A : ClockCall k) (base params : ℕ) (i : Fin A.d → ℕ) (s t : Store) : Prop where
  nat : ∀ x < params, (∀ v ∈ incidentVertices A.I, x ≠ rowCell A base i v ∧ x ≠ rowCell A base i v + 1) → t.nm x = s.nm x
  real : ∀ x < params, (∀ v ∈ incidentVertices A.I, x < rowCell A base i v + 4 ∨ rowCell A base i v + 4 + A.d ≤ x) → t.rm x = s.rm x

theorem ScanMemory.identical {k : ℕ} {A : ClockCall k} {base params : ℕ} {i : Fin A.d → ℕ}
    {s t : Store} (hn : t.nm = s.nm) (hr : t.rm = s.rm) : ScanMemory A base params i s t :=
  ⟨fun _ _ _ => congrFun hn _, fun _ _ _ => congrFun hr _⟩

theorem ScanMemory.trans {k : ℕ} {A : ClockCall k} {base params : ℕ} {i : Fin A.d → ℕ}
    {s t w : Store} (h : ScanMemory A base params i s t) (h' : ScanMemory A base params i t w) :
    ScanMemory A base params i s w := ⟨fun x hx hh => (h'.nat x hx hh).trans (h.nat x hx hh),
      fun x hx hh => (h'.real x hx hh).trans (h.real x hx hh)⟩

theorem CompareFrame.scan {k : ℕ} {A : ClockCall k} {base params v : ℕ} {i : Fin A.d → ℕ}
    {s t : Store} (h : CompareFrame params (rowCell A base i v) A.d s t) (hv : v ∈ incidentVertices A.I) :
    ScanMemory A base params i s t := ⟨fun x hx hh => h.nat x hx (hh v hv).1 (hh v hv).2,
      fun x hx hh => h.real x hx (hh v hv)⟩

theorem ScanMemory.after_row {k : ℕ} {A : ClockCall k} {base params : ℕ} {i : Fin A.d → ℕ}
    {s t : Store} (h : ScanMemory A base params i s t) (hi : ∀ r, i r < A.q) (x : ℕ) (hx : x < params)
    (he : extent A base ≤ x) : t.nm x = s.nm x ∧ t.rm x = s.rm x := by
  constructor
  · apply h.nat x hx
    intro v hv; have hh := row_end A base v i hv hi; omega
  · apply h.real x hx
    intro v hv; have hh := row_end A base v i hv hi; omega

theorem ScanMemory.before_row {k : ℕ} {A : ClockCall k} {base params : ℕ} {i : Fin A.d → ℕ}
    {s t : Store} (h : ScanMemory A base params i s t) (x : ℕ) (hx : x < params) (hb : x < base + 4) :
    t.nm x = s.nm x ∧ t.rm x = s.rm x := by
  have hh (v : ℕ) : base + 4 ≤ rowCell A base i v := by unfold rowCell scanAddress; omega
  exact ⟨h.nat x hx (fun v _ => by have := hh v; omega), h.real x hx (fun v _ => Or.inl (by have := hh v; omega))⟩

theorem ScanMemory.value {k : ℕ} {A : ClockCall k} {base params : ℕ} {i : Fin A.d → ℕ}
    {s t : Store} (h : ScanMemory A base params i s t) (hi : ∀ r, i r < A.q)
    (j : Fin A.d → ℕ) (hj : ∀ r, j r < A.q) (u : ℕ) (hu : u ∈ incidentVertices A.I) (hp : extent A base ≤ params) :
    t.rm (rowCell A base j u) = s.rm (rowCell A base j u) := by
  have he := row_end A base u j hu hj
  apply h.real _ (by omega)
  intro v hv
  by_contra! hbad
  let y := rowCell A base j u - rowCell A base i v
  have hsmall : y < A.d + 4 := by unfold y; omega
  have hg : rowCell A base j u + 0 = rowCell A base i v + y := by unfold y; omega
  have hy := (separated_cell_fields A base j i u v 0 y (incident_valid _ _ hu) (incident_valid _ _ hv)
    hj hi (by omega) hsmall hg).2.2
  unfold y at hy
  omega

theorem ScanMemory.rank {k : ℕ} {A : ClockCall k} {base params : ℕ} {i : Fin A.d → ℕ}
    {s t : Store} (h : ScanMemory A base params i s t) (hi : ∀ r, i r < A.q)
    (j : Fin A.d → ℕ) (hj : ∀ r, j r < A.q) (u : ℕ) (hu : u ∈ incidentVertices A.I) (hp : extent A base ≤ params) :
    t.nm (rowCell A base j u + 2) = s.nm (rowCell A base j u + 2) := by
  have he := row_end A base u j hu hj
  apply h.nat _ (by omega)
  intro v hv
  have hf (y : ℕ) (hy : y < 2) : rowCell A base j u + 2 ≠ rowCell A base i v + y := by
    intro hh
    have hz := (separated_cell_fields A base j i u v 2 y (incident_valid _ _ hu) (incident_valid _ _ hv)
      hj hi (by omega) (by omega) hh).2.2
    omega
  exact ⟨by simpa only [Nat.add_zero] using hf 0 (by decide), hf 1 (by decide)⟩

theorem ScanMemory.grid {k : ℕ} {A : ClockCall k} {base params u : ℕ} {i : Fin A.d → ℕ}
    {s t : Store} (h : ScanMemory A base params i s t) (hi : ∀ r, i r < A.q)
    (hu : u ∈ incidentVertices A.I) (hp : extent A base ≤ params) (T : MultiTable A.d) (hg : GridValues A base u i T s) :
    GridValues A base u i T t := fun a ha =>
  (h.value hi _ ((rectangle_mem A i a).mp ha) u hu hp).trans (hg a ha)

theorem guarded_table {k : ℕ} (A : ClockCall k) (i : Fin A.d → ℕ) (u : ℕ) (S : MultiLayer A.d) (e : ℕ × ℕ) :
    (guarded A i u S e).table = S.table := by
  unfold guarded
  split <;> simp [relax_table]

end NearLinearRSP.TwoResources.Supplement.LayerRAM

end

section

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace NearLinearRSP.TwoResources.Supplement.LayerRAM
open Mission.Structured Mission.Preprocess TableQuery
open Mission.Queue (activeLeaf)

theorem advance_fields (links e next : ℕ) (input : RAMInput) (s : Store)
    (ht : s.nr 194 = e + 1) (hl : s.nr 164 = links) (hn : s.nm (links + e) = next) :
    let p := evalAtoms input advanceLink s
    p.nr 75 = e ∧ p.nr 194 = next ∧ (∀ r, r ≠ 75 → r ≠ 86 → r ≠ 194 → p.nr r = s.nr r) ∧
      p.rr = s.rr ∧ p.nm = s.nm ∧ p.rm = s.rm := by
  simp +contextual [advanceLink, evalAtoms, Atom.eval, Store.at, Store.ofRAM, ramStep, evalNat, ht, hl, hn,
    Function.update_of_ne]

theorem advance_context {k : ℕ} {A : ClockCall k} {base params B W P u : ℕ} {i : Fin A.d → ℕ}
    {s t : Store} (h : EdgeContext A base params B W P u i s)
    (hn : ∀ r, r ≠ 75 → r ≠ 86 → r ≠ 194 → t.nr r = s.nr r) (hr : t.rr = s.rr) :
    EdgeContext A base params B W P u i t := by
  have hc := h.toRowControl.transfer (fun a ha => hn a (control_addresses ha).2.1
    (control_addresses ha).2.2.1 (control_addresses ha).2.2.2.2.1) (fun a _ _ => congrFun hr a)
  exact ⟨hc, (hn 97 (by decide) (by decide) (by decide)).trans h.source,
    (hn 99 (by decide) (by decide) (by decide)).trans h.address⟩

structure ScanState {k : ℕ} (A : ClockCall k) (base map params B W P u : ℕ) (i : Fin A.d → ℕ)
    (S : MultiLayer A.d) (s : Store) : Prop where
  ctx : EdgeContext A base params B W P u i s
  heap : Heap B W P (activeLeaf (incidentVertices A.I) S.queue S.keys B) s
  parents : ParentRecords A base i S.parents s
  grid : GridValues A base u i S.table s
  coords : ∀ r : Fin A.d, s.nm (8 + r.val) = (A.coords.get r).val
  mapReg : s.nr 141 = map
  linksReg : s.nr 164 = map + 3 * A.I.graph.n
  indices : ∀ v ∈ incidentVertices A.I, s.nm (map + v) = (incidentVertices A.I).idxOf v + 1

theorem ScanState.visit {k : ℕ} (A : ClockCall k) (hk : 0 < k) (ε : ℝ) (base map params B W P u v e next : ℕ)
    (i : Fin A.d → ℕ) (S : MultiLayer A.d) (s : Store) (he : A.I.graph.edges[e]? = some (u,v))
    (hi : ∀ r, i r < A.q) (hB : (incidentVertices A.I).length ≤ B) (hhead : 8 + k ≤ base)
    (hmap : extent A base ≤ map) (hsep : map + 3 * A.I.graph.n + A.I.graph.edges.length ≤ params)
    (hW : params + 2 * A.d ≤ W) (h : ScanState A base map params B W P u i S s)
    (ht : s.nr 194 = e + 1) (hl : s.nm (map + 3 * A.I.graph.n + e) = next) :
    let U := guarded A i u S (u,v)
    ∃ t n, Run (multiInput A.I ε) (.seq (.atoms advanceLink) (visitEdge k A.d)) s t n ∧
      ScanState A base map params B W P u i U t ∧ t.nr 194 = next ∧ ScanMemory A base params i s t ∧
      n ≤ visitCost k A.d A.q B + 4 := by
  let input := multiInput A.I ε
  let p := evalAtoms input advanceLink s
  have hu : u ∈ incidentVertices A.I := activeVertices_edge_left (lengthInstance A.I) u v (List.mem_of_getElem? he)
  have hv : v ∈ incidentVertices A.I := activeVertices_edge_right (lengthInstance A.I) u v (List.mem_of_getElem? he)
  obtain ⟨h75, h194, regs, reals, natM, realM⟩ := advance_fields _ e next input s ht h.linksReg hl
  have ph : EdgeContext A base params B W P u i p := advance_context h.ctx regs reals
  have pidx : p.nm (p.nr 141 + v) = (incidentVertices A.I).idxOf v + 1 := by
    change s.nm (p.nr 141 + v) = _
    rw [regs 141 (by decide) (by decide) (by decide), h.mapReg]; exact h.indices v hv
  obtain ⟨t, n, hr, heap, parents, frame, cost⟩ := visit_edge_run A hk ε base params B W P u v e i S p he hi hB
    (by omega) hW ph h75 (h.heap.memory natM realM) h.parents h.grid h.coords pidx
  have f := visiting_frame hr
  have gf : ScanMemory A base params i s t := (ScanMemory.identical natM realM).trans (frame.scan hv)
  have reg (r : ℕ) (hr : r ≤ 200) (hs : StableNat r) := f.nat r (by unfold EdgeRAM.bank; omega) hs
  have hc : EdgeContext A base params B W P u i t := ph.frame f
  have gd : GridValues A base u i (guarded A i u S (u,v)).table t := by
    rw [guarded_table]; exact gf.grid hi hu (by omega) S.table h.grid
  refine ⟨t, 4+n, Run.seq (run_atoms input advanceLink s) hr, ⟨hc, heap, parents, gd, ?_, ?_, ?_, ?_⟩,
    (reg 194 (by decide) (by norm_num [StableNat])).trans h194, gf, by omega⟩
  · intro r
    have hr := r.isLt
    have hd : A.d ≤ k := clockCoordinates_length_le A.I
    have hb : base + 4 ≤ extent A base := by unfold extent; omega
    exact ((gf.before_row _ (by omega) (by omega)).1).trans (h.coords r)
  · exact (reg 141 (by decide) (by norm_num [StableNat])).trans ((regs 141 (by decide) (by decide) (by decide)).trans h.mapReg)
  · exact (reg 164 (by decide) (by norm_num [StableNat])).trans ((regs 164 (by decide) (by decide) (by decide)).trans h.linksReg)
  · intro w hw
    have hn := incident_valid A.I w hw
    exact ((gf.after_row hi _ (by omega) (by omega)).1).trans (h.indices w hw)

end NearLinearRSP.TwoResources.Supplement.LayerRAM

end

section

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace NearLinearRSP.TwoResources.Supplement.LayerRAM
open Mission.Structured Mission.Preprocess TableQuery

theorem neighbor_loop_run {k : ℕ} (A : ClockCall k) (hk : 0 < k) (ε : ℝ) (base map params B W P u : ℕ)
    (i : Fin A.d → ℕ) (hi : ∀ r, i r < A.q) (hB : (incidentVertices A.I).length ≤ B) (hhead : 8 + k ≤ base)
    (hmap : extent A base ≤ map) (hsep : map + 3 * A.I.graph.n + A.I.graph.edges.length ≤ params)
    (hW : params + 2 * A.d ≤ W) (es : List ℕ) (token : ℕ) (S : MultiLayer A.d) (s : Store)
    (h : ScanState A base map params B W P u i S s) (ht : s.nr 194 = token)
    (hchain : AdjacencyChain s.nm (map + 3 * A.I.graph.n) token es)
    (hvalid : ∀ e ∈ es, ∃ v, A.I.graph.edges[e]? = some (u,v)) :
    let U := es.foldl (fun R e => guarded A i u R (edgeAt (lengthInstance A.I) e)) S
    ∃ t n, Run (multiInput A.I ε) (scanNeighbors k A.d) s t n ∧
      ScanState A base map params B W P u i U t ∧ ScanMemory A base params i s t ∧
      n ≤ (visitCost k A.d A.q B + 6) * es.length + 1 := by
  induction es generalizing token S s with
  | nil =>
    cases hchain
    exact ⟨s, 1, Run.loopFalse (by simp [Guard.eval, natTest, ht, h.ctx.zero]), h, ScanMemory.identical rfl rfl, by simp⟩
  | cons e es ih =>
    cases hchain with
    | cons hnext htail =>
      obtain ⟨v, he⟩ := hvalid e (by simp)
      obtain ⟨p, c, hp, hstate, htoken, hf, hc⟩ := h.visit A hk ε base map params B W P u v e _ i S s he hi
        hB hhead hmap hsep hW ht hnext
      have tail := htail.frame (mem' := p.nm) (by
        intro j hj
        obtain ⟨w, hw⟩ := hvalid j (List.mem_cons_of_mem _ hj)
        have hjlt := (List.getElem?_eq_some_iff.mp hw).1
        exact (hf.after_row hi _ (by omega) (by omega)).1)
      obtain ⟨t, m, hr, doneState, hframe, hm⟩ := ih _ _ p hstate htoken tail (fun j hj => hvalid j (List.mem_cons_of_mem _ hj))
      have hg : (Guard.nat .lt 30 194).eval s = true := by simp [Guard.eval, natTest, ht, h.ctx.zero]
      have hedge : edgeAt (lengthInstance A.I) e = (u,v) := by change A.I.graph.edges[e]?.getD (0,0) = _; simp [he]
      simp only [List.foldl_cons, hedge, List.length_cons]
      refine ⟨t, _, Run.loopTrue hg hp hr, doneState, hf.trans hframe, ?_⟩
      rw [Nat.mul_succ]
      omega

theorem outgoing_run {k : ℕ} (A : ClockCall k) (hk : 0 < k) (ε : ℝ) (base map params B W P u : ℕ)
    (i : Fin A.d → ℕ) (S : MultiLayer A.d) (s : Store) (hu : u ∈ incidentVertices A.I) (hi : ∀ r, i r < A.q)
    (hB : (incidentVertices A.I).length ≤ B) (hhead : 8 + k ≤ base) (hmap : extent A base ≤ map)
    (hsep : map + 3 * A.I.graph.n + A.I.graph.edges.length ≤ params) (hW : params + 2 * A.d ≤ W)
    (h : ScanState A base map params B W P u i S s) (hheads : s.nr 163 = map + 2 * A.I.graph.n)
    (adj : AdjacencyPrefix (lengthInstance A.I) A.I.graph.edges.length (map + 2 * A.I.graph.n) (map + 3 * A.I.graph.n) s.nm) :
    let U := (callEdges A).foldl (relax A i u) S
    let es := outgoingIndices (lengthInstance A.I) A.I.graph.edges.length u
    ∃ t n, Run (multiInput A.I ε) (relaxNeighbors k A.d) s t n ∧
      ScanState A base map params B W P u i U t ∧ ScanMemory A base params i s t ∧
      n ≤ (visitCost k A.d A.q B + 6) * es.length + 3 := by
  let input := multiInput A.I ε
  let p := evalAtoms input firstNeighbor s
  have reg (a : ℕ) (ha : a ≠ 86) (hb : a ≠ 194) : p.nr a = s.nr a := by
    simp [p, firstNeighbor, evalAtoms, Atom.eval, Store.ofRAM, Store.at, ramStep, Function.update_of_ne ha, Function.update_of_ne hb]
  have token : p.nr 194 = s.nm (map + 2 * A.I.graph.n + u) := by
    simp [p, firstNeighbor, evalAtoms, Atom.eval, Store.ofRAM, Store.at, ramStep, evalNat, hheads, h.ctx.source]
  have ph : ScanState A base map params B W P u i S p :=
    ⟨advance_context h.ctx (fun a _ h1 h2 => reg a h1 h2) rfl, h.heap.memory rfl rfl, h.parents, h.grid, h.coords,
      (reg 141 (by decide) (by decide)).trans h.mapReg, (reg 164 (by decide) (by decide)).trans h.linksReg, h.indices⟩
  obtain ⟨t, c, hr, hd, hf, hc⟩ := neighbor_loop_run A hk ε base map params B W P u i hi hB hhead hmap hsep hW _ _ S p ph
    token (adj u (incident_valid A.I u hu)) (fun e he => outgoingIndices_valid (lengthInstance A.I) u e he)
  rw [linked_relaxations] at hd
  exact ⟨t, 2+c, Run.seq (run_atoms input firstNeighbor s) hr, hd, (ScanMemory.identical (s := s) (t := p) rfl rfl).trans hf, by omega⟩

end NearLinearRSP.TwoResources.Supplement.LayerRAM

end

section

set_option autoImplicit false
set_option maxHeartbeats 1800000

namespace NearLinearRSP.TwoResources.Supplement.LayerRAM
open Mission.Structured TableQuery

theorem Numbers.grid {k : ℕ} {A : ClockCall k} {base : ℕ} {T : MultiTable A.d} {s : Store}
    (h : Numbers A base T s) (u : ℕ) (hu : u ∈ incidentVertices A.I) (i : Fin A.d → ℕ) :
    GridValues A base u i T s := by
  intro a ha
  have hj := (rectangle_mem A i a).mp ha
  rw [value_of_valid A T u _ hj]
  exact (h u hu _ hj).1

theorem Numbers.congr {k : ℕ} {A : ClockCall k} {base : ℕ} {T : MultiTable A.d} {s t : Store}
    (h : Numbers A base T s) (hf : ∀ x < extent A base, t.nm x = s.nm x ∧ t.rm x = s.rm x) :
    Numbers A base T t := by
  intro v hv j hj
  have he := row_end A base v j hv hj
  obtain ⟨hval, hrank⟩ := h v hv j hj
  exact ⟨((hf _ (by omega)).2).trans hval, ((hf _ (by omega)).1).trans hrank⟩

theorem Numbers.scan {k : ℕ} {A : ClockCall k} {base params : ℕ} {T : MultiTable A.d} {s t : Store}
    {i : Fin A.d → ℕ} (h : Numbers A base T s) (hf : ScanMemory A base params i s t)
    (hi : ∀ r, i r < A.q) (hp : extent A base ≤ params) : Numbers A base T t := by
  intro v hv j hj
  obtain ⟨hval, hrank⟩ := h v hv j hj
  exact ⟨(hf.value hi j hj v hv hp).trans hval, (hf.rank hi j hj v hv hp).trans hrank⟩

theorem Numbers.settled {k : ℕ} (A : ClockCall k) (base u : ℕ) (i : Fin A.d → ℕ) (c : MultiCell)
    (T : MultiTable A.d) (s t : Store) (hu : u ∈ incidentVertices A.I) (hi : ∀ r, i r < A.q)
    (h : Numbers A base T s) (hn : t.nm = Function.update s.nm (rowCell A base i u + 2) c.rank)
    (hr : t.rm = Function.update s.rm (rowCell A base i u) (1 - c.value)) : Numbers A base (put T u i c) t := by
  intro v hv j hj
  dsimp only
  by_cases he : v = u ∧ j = i
  · obtain ⟨rfl, rfl⟩ := he
    simp [put_same, hn, hr]
  · have hcell : rowCell A base j v ≠ rowCell A base i u := by
      intro hx
      have hh := separated_cell_fields A base j i v u 0 0 (incident_valid _ _ hv) (incident_valid _ _ hu)
        hj hi (by omega) (by omega) (by simpa only [Nat.add_zero] using hx)
      exact he ⟨hh.2.1, hh.1⟩
    rw [put_other T u v i j c (by tauto)]
    simpa only [hn, hr, Function.update_of_ne hcell, Function.update_of_ne
      (show rowCell A base j v + 2 ≠ rowCell A base i u + 2 by omega)] using h v hv j hj

theorem ParentRecords.settled {k : ℕ} (A : ClockCall k) (base u : ℕ) (i : Fin A.d → ℕ) (p : ℕ → MultiParent)
    (s t : Store) (rank : ℕ) (key : ℝ) (hu : u ∈ incidentVertices A.I) (hi : ∀ r, i r < A.q)
    (h : ParentRecords A base i p s) (hn : t.nm = Function.update s.nm (rowCell A base i u + 2) rank)
    (hr : t.rm = Function.update s.rm (rowCell A base i u) (1 - key)) : ParentRecords A base i p t := by
  intro v hv
  have diff (x y : ℕ) (hx : x < A.d + 4) (hy : y < A.d + 4) (hne : x ≠ y) :
      rowCell A base i v + x ≠ rowCell A base i u + y :=
    fun h => hne (separated_cell_fields A base i i v u x y (incident_valid _ _ hv) (incident_valid _ _ hu) hi hi hx hy h).2.2
  have h0 : rowCell A base i v ≠ rowCell A base i u + 2 := by simpa only [Nat.add_zero] using diff 0 2 (by omega) (by omega) (by decide)
  have h1 := diff 1 2 (by omega) (by omega) (by decide)
  obtain ⟨ht, hp, hg⟩ := h v hv
  refine ⟨by simpa only [hn, Function.update_of_ne h0] using ht, by simpa only [hn, Function.update_of_ne h1] using hp, ?_⟩
  intro w hw r
  have hl := r.isLt
  have h4 : rowCell A base i v + 4 + r.val ≠ rowCell A base i u := by
    simpa only [Nat.add_zero, Nat.add_assoc] using diff (4+r.val) 0 (by omega) (by omega) (by omega)
  simpa only [hr, Function.update_of_ne h4] using hg w hw r

end NearLinearRSP.TwoResources.Supplement.LayerRAM

end

section

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace NearLinearRSP.TwoResources.Supplement.LayerRAM
open Mission.Structured Mission.Preprocess TableQuery

def OutsideRow {k : ℕ} (A : ClockCall k) (base : ℕ) (i : Fin A.d → ℕ) (x : ℕ) : Prop :=
  ∀ v ∈ incidentVertices A.I, x < rowCell A base i v ∨ rowCell A base i v + (A.d + 4) ≤ x
def RowFrame {k : ℕ} (A : ClockCall k) (base lim : ℕ) (i : Fin A.d → ℕ) (s t : Store) : Prop :=
  ∀ x < lim, OutsideRow A base i x → t.nm x = s.nm x ∧ t.rm x = s.rm x

theorem RowFrame.trans {k : ℕ} {A : ClockCall k} {base lim : ℕ} {i : Fin A.d → ℕ} {s p t : Store}
    (h : RowFrame A base lim i s p) (h' : RowFrame A base lim i p t) : RowFrame A base lim i s t := by
  intro x hx hs
  exact ⟨(h' x hx hs).1.trans (h x hx hs).1, (h' x hx hs).2.trans (h x hx hs).2⟩

theorem ScanMemory.row_frame {k : ℕ} {A : ClockCall k} {base lim : ℕ} {i : Fin A.d → ℕ} {s t : Store}
    (h : ScanMemory A base lim i s t) : RowFrame A base lim i s t := by
  intro x hx hs
  exact ⟨h.nat x hx (fun v hv => by have := hs v hv; omega),
    h.real x hx (fun v hv => by have := hs v hv; omega)⟩

theorem RowFrame.after {k : ℕ} {A : ClockCall k} {base lim : ℕ} {i : Fin A.d → ℕ} {s t : Store}
    (h : RowFrame A base lim i s t) (hi : ∀ r, i r < A.q) (x : ℕ) (hx : x < lim) (hb : extent A base ≤ x) :
    t.nm x = s.nm x ∧ t.rm x = s.rm x := h x hx (fun v hv => Or.inr (by have := row_end A base v i hv hi; omega))

theorem RowFrame.before {k : ℕ} {A : ClockCall k} {base lim : ℕ} {i : Fin A.d → ℕ} {s t : Store}
    (h : RowFrame A base lim i s t) (x : ℕ) (hx : x < lim) (hb : x < base + 4) :
    t.nm x = s.nm x ∧ t.rm x = s.rm x := h x hx (fun v _ => Or.inl (by unfold rowCell scanAddress; omega))

theorem outside_other_row {k : ℕ} (A : ClockCall k) (base : ℕ) (i j : Fin A.d → ℕ) (v x : ℕ)
    (hi : ∀ r, i r < A.q) (hj : ∀ r, j r < A.q) (hv : v ∈ incidentVertices A.I) (hx : x < A.d + 4) (hne : j ≠ i) :
    OutsideRow A base i (rowCell A base j v + x) := by
  intro u hu
  by_contra! hbad
  let y := rowCell A base j v + x - rowCell A base i u
  have hy : y < A.d + 4 := by unfold y; omega
  have eq : rowCell A base j v + x = rowCell A base i u + y := by unfold y; omega
  exact hne (separated_cell_fields A base j i v u x y (incident_valid _ _ hv) (incident_valid _ _ hu) hj hi hx hy eq).1

theorem graph_transport {k : ℕ} (I : MultiInstance k) (map : ℕ) (s t : Store) (h : GraphRAM.Image I map s)
    (r141 : t.nr 141 = s.nr 141) (r142 : t.nr 142 = s.nr 142) (r143 : t.nr 143 = s.nr 143)
    (hf : ∀ x, map ≤ x → x < map + 3 * I.graph.n + I.graph.edges.length → t.nm x = s.nm x) :
    GraphRAM.Image I map t := by
  have hlen := h.vertices.length_le
  refine ⟨h.vertices.congr r141 r142 r143 (fun v hv => hf _ (by omega) (by omega)) (fun j hj => hf _ (by omega) (by omega)), ?_⟩
  intro v hv
  have hh := hf (map + 2 * I.graph.n + v) (by omega) (by change v < I.graph.n at hv; omega)
  rw [hh]
  apply (h.outgoing v hv).frame
  intro e he
  have hi := outgoingIndices_lt (lengthInstance I) I.graph.edges.length v e he
  apply hf _ (by omega) (by omega)

end NearLinearRSP.TwoResources.Supplement.LayerRAM

end

section

set_option autoImplicit false
set_option maxHeartbeats 1700000

namespace NearLinearRSP.TwoResources.Supplement.LayerRAM
open Mission.Structured Mission.Preprocess TableQuery
open Mission.Queue (activeLeaf)

structure LayerImage {k : ℕ} (A : ClockCall k) (base map params B W P : ℕ) (i : Fin A.d → ℕ)
    (S : MultiLayer A.d) (s : Store) : Prop where
  control : RowControl A base params B W P i s
  graph : GraphRAM.Image A.I map s
  heads : s.nr 163 = map + 2 * A.I.graph.n
  links : s.nr 164 = map + 3 * A.I.graph.n
  coords : ∀ r : Fin A.d, s.nm (8 + r.val) = (A.coords.get r).val
  heap : Heap B W P (activeLeaf (incidentVertices A.I) S.queue S.keys B) s
  rank : s.nr 191 = S.nextRank
  numbers : Numbers A base S.table s
  parents : ParentRecords A base i S.parents s
  queued : S.queue.Sublist (incidentVertices A.I)

theorem pop_control {k : ℕ} {A : ClockCall k} {base params B W P : ℕ} {i : Fin A.d → ℕ} {s t : Store}
    {input : RAMInput} {n : ℕ} (h : RowControl A base params B W P i s) (hr : Run input popCmd s t n) :
    RowControl A base params B W P i t := by
  have hn : ∀ r ∈ popCmd.natWrites, r < 30 ∨ r = 95 ∨ r = 96 ∨ r = 97 := by decide
  have hreal : ∀ r ∈ popCmd.realWrites, r < 30 ∨ r = 94 := by decide
  apply h.transfer
  · intro a ha
    apply hr.nat_frame
    intro hm
    have hw := hn a hm
    have hh := control_addresses ha
    omega
  · intro a h80 h83
    apply hr.real_frame
    intro hm; have := hreal a hm; omega

theorem outgoing_register {k d n : ℕ} {input : RAMInput} {s t : Store} (h : Run input (relaxNeighbors k d) s t n)
    (a : ℕ) (hb : a < EdgeRAM.bank k) (ha : StableNat a) (h194 : a ≠ 194) : t.nr a = s.nr a := by
  apply h.nat_frame
  have hn := (visit_registers k d a hb).1 ha
  unfold StableNat at ha
  simp [relaxNeighbors, scanNeighbors, advanceLink, firstNeighbor, Cmd.atoms, Cmd.natWrites, Atom.natWrites, hn, h194]
  omega

theorem LayerImage.scan_state {k : ℕ} {A : ClockCall k} {base map params B W P u : ℕ} {i : Fin A.d → ℕ}
    {S : MultiLayer A.d} {s : Store} (h : LayerImage A base map params B W P i S s) (hu : u ∈ incidentVertices A.I)
    (hs : s.nr 97 = u) (ha : s.nr 99 = rowCell A base i u) :
    ScanState A base map params B W P u i S s :=
  ⟨⟨h.control, hs, ha⟩, h.heap, h.parents, h.numbers.grid u hu i, h.coords, h.graph.vertices.base_reg, h.links,
    fun v hv => by simpa only [h.graph.vertices.base_reg] using probe_index _ _ _ _ v s h.graph.vertices hv⟩

theorem relax_image {k : ℕ} (A : ClockCall k) (hk : 0 < k) (ε : ℝ) (base map params B W P u : ℕ)
    (i : Fin A.d → ℕ) (S : MultiLayer A.d) (s : Store) (site : Site A base map params B W)
    (hi : ∀ r, i r < A.q) (h : LayerImage A base map params B W P i S s) (hu : u ∈ incidentVertices A.I)
    (hs : s.nr 97 = u) (ha : s.nr 99 = rowCell A base i u) :
    ∃ t n, Run (multiInput A.I ε) (relaxNeighbors k A.d) s t n ∧
      LayerImage A base map params B W P i (relaxAll A i u S) t ∧ RowFrame A base params i s t ∧
      n ≤ (visitCost k A.d A.q B + 6) * (outgoingIndices (lengthInstance A.I) A.I.graph.edges.length u).length + 3 := by
  obtain ⟨t, n, hr, hd, hf, hc⟩ := outgoing_run A hk ε base map params B W P u i S s hu hi site.capacity site.header
    site.publicEnd site.graphEnd site.workspace (h.scan_state hu hs ha) h.heads h.graph.outgoing
  have reg (a : ℕ) (ha : a ≤ 200) (hh : StableNat a) (hn : a ≠ 194) := outgoing_register hr a (by unfold EdgeRAM.bank; omega) hh hn
  have fixed (a : ℕ) (hl : 101 ≤ a) (hh : a ≤ 193) := reg a (by omega) (by unfold StableNat; omega) (by omega)
  have im := graph_transport A.I map s t h.graph (fixed 141 (by omega) (by omega)) (fixed 142 (by omega) (by omega))
    (fixed 143 (by omega) (by omega)) (fun x hl hh => (hf.after_row hi _ (hh.trans_le site.graphEnd) (site.publicEnd.trans hl)).1)
  refine ⟨t, n, hr, ⟨hd.ctx.toRowControl, im, (fixed 163 (by omega) (by omega)).trans h.heads, hd.linksReg,
    hd.coords, hd.heap, ?_, ?_, hd.parents, ?_⟩, hf.row_frame, hc⟩
  · rw [relaxAll_nextRank]
    exact (fixed 191 (by omega) (by omega)).trans h.rank
  · rw [relaxAll_table]
    exact h.numbers.scan hf hi (site.publicEnd.trans (by have := site.graphEnd; omega))
  · rw [relaxAll_queue]; exact h.queued

end NearLinearRSP.TwoResources.Supplement.LayerRAM

end

section

set_option autoImplicit false
set_option maxHeartbeats 1700000

namespace NearLinearRSP.TwoResources.Supplement.LayerRAM
open Mission.Structured Mission.Preprocess TableQuery

structure RowInput {k : ℕ} (A : ClockCall k) (base map keys params B W P : ℕ) (i : Fin A.d → ℕ)
    (T : MultiTable A.d) (s : Store) : Prop where
  control : RowControl A base params B W P i s
  graph : GraphRAM.Image A.I map s
  heads : s.nr 163 = map + 2 * A.I.graph.n
  links : s.nr 164 = map + 3 * A.I.graph.n
  coords : ∀ r : Fin A.d, s.nm (8 + r.val) = (A.coords.get r).val
  keys : s.nr 189 = keys
  source : s.nm 1 = A.I.source
  numbers : Numbers A base T s

theorem begin_fields (input : RAMInput) (s : Store) :
    let p := evalAtoms input beginRow s
    p.nr 5 = s.nm 1 ∧ p.nr 31 = 1 ∧ p.nr 191 = 0 ∧ ∀ a, a ≠ 5 → a ≠ 31 → a ≠ 86 → a ≠ 191 → p.nr a = s.nr a := by
  simp +contextual [beginRow, evalAtoms, Atom.eval, Store.at, Store.ofRAM, ramStep, Function.update_of_ne]

theorem start_nat (d a : ℕ) (ha : 30 ≤ a) (h49 : a ≠ 49) (h76 : a ≠ 76) (h93 : a ≠ 93)
    (hr : a < 86 ∨ 90 < a) : a ∉ (startLayer d).natWrites := by
  have hc := copies_preserve 49 76 (d+4) a h49
  have hs := scan_registers (List.range d) a hr
  have ht : ∀ j ∈ buildHeap.natWrites, j < 30 := by decide
  have hb : a ∉ buildHeap.natWrites := fun hh => (Nat.not_lt_of_ge ha) (ht _ hh)
  simp [startLayer, seedAll, seedZero, seedVertex, vertexCmd, vertexOps, seedCmd, sourceOps, beginScan, commitSeed,
    Cmd.atoms, Cmd.natWrites, Atom.natWrites, hc, hs, hb, h49, h76, h93]
  omega

theorem scan_reals (rs : List ℕ) (a : ℕ) (h1 : 80 ≤ a) (h2 : a ≤ 83) : a ∉ (scan rs).realWrites := by
  induction rs with
  | nil => simp [scan, Cmd.realWrites]
  | cons r rs ih =>
    have h : a ∉ (step r).realWrites := by
      simp [step, probe, increment, fetchOps, saturated, choose, saveOps, Cmd.atoms, Cmd.realWrites, Atom.realWrites]
      omega
    simp [scan, Cmd.realWrites, h, ih]

theorem start_real (d a : ℕ) (h1 : 80 ≤ a) (h2 : a ≤ 83) : a ∉ (startLayer d).realWrites := by
  have ht : ∀ j ∈ buildHeap.realWrites, j < 30 := by decide
  have hb : a ∉ buildHeap.realWrites := fun hh => (show ¬a<30 by omega) (ht _ hh)
  have hc := (EdgeRAM.copies_readonly 49 76 (d+4)).2.2
  have hs := scan_reals (List.range d) a h1 h2
  simp [startLayer, seedAll, seedZero, seedVertex, vertexCmd, vertexOps, seedCmd, sourceOps, beginScan, commitSeed,
    Cmd.atoms, Cmd.realWrites, Atom.realWrites, hb, hc, hs]
  omega

theorem control_start {d a : ℕ} (ha : ControlNat d a) :
    a ≠ 5 ∧ a ≠ 31 ∧ a ≠ 86 ∧ a ≠ 191 ∧ a ∉ (startLayer d).natWrites := by
  simp only [ControlNat, List.mem_cons, List.not_mem_nil, or_false, stateReg, strideReg, CandidateRAM.current] at ha
  rcases ha with h | ⟨r, hr, h⟩ <;> exact ⟨by omega, by omega, by omega, by omega, start_nat d a (by omega) (by omega) (by omega) (by omega) (by omega)⟩

theorem row_ready {k : ℕ} (A : ClockCall k) (T : MultiTable A.d) (base map keys params B W P : ℕ)
    (i : Fin A.d → ℕ) (hi : ∀ r, i r < A.q) (input : RAMInput) (s : Store) (h : RowInput A base map keys params B W P i T s) :
    let p := evalAtoms input beginRow s
    Row A T base (map + A.I.graph.n) keys i p ∧ RowControl A base params B W P i p := by
  let p := evalAtoms input beginRow s
  obtain ⟨source, one, _, reg⟩ := begin_fields input s
  have ctrl : RowControl A base params B W P i p := h.control.transfer (fun a ha => by
    obtain ⟨h1,h2,h3,h4,_⟩ := control_start ha; exact reg a h1 h2 h3 h4) (fun _ _ _ => rfl)
  refine ⟨⟨ctrl.zero, one, ctrl.q, source.trans h.source, ctrl.row, (reg 142 (by decide) (by decide) (by decide) (by decide)).trans h.graph.vertices.array_reg,
    (reg 143 (by decide) (by decide) (by decide) (by decide)).trans h.graph.vertices.count_reg,
    (reg 189 (by decide) (by decide) (by decide) (by decide)).trans h.keys, ctrl.counts, ctrl.strides, ?_, ?_⟩, ctrl⟩
  · intro j hj
    apply h.graph.vertices.value
    simp [vertexAt, Mission.Queue.slotVertex, List.getElem?_eq_getElem hj]
  · intro v hv r hh
    have hj : ∀ z, Function.update i r (i r + 1) z < A.q := by
      intro z; by_cases hz : z = r
      · subst z; simpa using hh
      · simpa only [Function.update_of_ne hz] using hi z
    unfold nextValue
    rw [value_of_valid _ _ _ _ hj]
    exact (h.numbers v hv _ hj).1

end NearLinearRSP.TwoResources.Supplement.LayerRAM

end

section

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace NearLinearRSP.TwoResources.Supplement.LayerRAM
open Mission.Structured Mission.Preprocess TableQuery
open Mission.Queue (activeLeaf)

theorem extract_image {k : ℕ} (A : ClockCall k) (base map params height W P : ℕ) (i : Fin A.d → ℕ)
    (S : MultiLayer A.d) (input : RAMInput) (s : Store) (site : Site A base map params (2 ^ height) W)
    (hi : ∀ r, i r < A.q) (h : LayerImage A base map params (2 ^ height) W P i S s) (hne : S.queue ≠ []) :
    let u := picked A S
    ∃ t n, Run input (extractVertex A.d) s t n ∧ LayerImage A base map params (2 ^ height) W P i (settle S u i) t ∧
      t.nr 97 = u ∧ t.nr 99 = rowCell A base i u ∧ RowFrame A base params i s t ∧
      n ≤ A.d + 19 * Nat.clog 2 (2 * 2 ^ height) + 34 := by
  let xs := incidentVertices A.I
  let u := picked A S
  let a := rowCell A base i u
  have hu : u ∈ xs := h.queued.subset (picked_mem A S hne)
  have hb := site.publicEnd
  have hg := site.graphEnd
  have hw := site.workspace
  have enda : a + 4 + A.d ≤ extent A base := row_end A base u i hu hi
  obtain ⟨p, c, he, hpu, hpk, hpheap, hkeep, hc⟩ := pop_heap xs S.queue S.keys height W P A.I.source input s h.control.cfg
    h.heap (incident_nodup A.I) h.queued site.capacity hne (fun v hv => by
      rw [h.graph.vertices.array_reg]
      exact h.graph.vertices.value (xs.idxOf v) v (show xs[xs.idxOf v]? = some v by simp [List.getElem?_idxOf, hv]))
  change p.nr 97 = u at hpu
  change p.rr 94 = S.keys u at hpk
  have pctrl := pop_control h.control he
  have prank : p.nr 191 = S.nextRank := (he.nat_frame 191 (by decide)).trans h.rank
  obtain ⟨t, ht, addr, rank, natmem, realmem, natreg, realreg⟩ :=
    settle_run A base i u S.nextRank (S.keys u) input p pctrl.row hpu hpk prank
  change t.nm = Function.update p.nm (a + 2) S.nextRank at natmem
  change t.rm = Function.update p.rm a (1 - S.keys u) at realmem
  have below (x : ℕ) (hx : x < W) := hkeep x (Or.inl hx)
  have pnum := h.numbers.congr (fun x hx => below x (by omega))
  have ppar := h.parents.congr hi (fun x hx => below x (by omega))
  have tnum := Numbers.settled A base u i ⟨S.keys u,S.parents u,S.nextRank⟩ S.table p t hu hi pnum natmem realmem
  have tpar := ParentRecords.settled A base u i S.parents p t S.nextRank (S.keys u) hu hi ppar natmem realmem
  have tctrl := pctrl.transfer (fun x hx => natreg x (by have := control_addresses hx; omega)
    (by have := control_addresses hx; omega) (by have := control_addresses hx; omega)) (fun x h1 h2 => realreg x (by omega))
  have above (x : ℕ) (hx : W ≤ x) : t.nm x = p.nm x ∧ t.rm x = p.rm x := by
    simp only [natmem, realmem, Function.update_of_ne (show x ≠ a + 2 by omega), Function.update_of_ne (show x ≠ a by omega), and_self]
  have theap := hpheap.congr (fun j _ => above _ (by omega)) (fun j _ => (above _ (by have := hpheap.disjoint; omega)).1)
  have frame : RowFrame A base params i s t := by
    intro x hx hs
    have hh := hs u hu
    change x < a ∨ a + (A.d + 4) ≤ x at hh
    simpa only [natmem, realmem, Function.update_of_ne (show x ≠ a + 2 by omega), Function.update_of_ne (show x ≠ a by omega)] using below x (by omega)
  have reg (x : ℕ) (h1 : x ≠ 99) (h2 : x ≠ 191) (h3 : x ≠ 86) (h4 : x ∉ popCmd.natWrites) : t.nr x = s.nr x :=
    (natreg x h1 h2 h3).trans (he.nat_frame x h4)
  have tgraph := graph_transport A.I map s t h.graph (reg 141 (by decide) (by decide) (by decide) (by decide))
    (reg 142 (by decide) (by decide) (by decide) (by decide)) (reg 143 (by decide) (by decide) (by decide) (by decide))
    (fun x hl hh => (frame.after hi x (by omega) (by omega)).1)
  refine ⟨t, c + (A.d + 13), Run.seq he ht, ⟨tctrl, tgraph, ?_, ?_, ?_, theap, rank, tnum, tpar, List.erase_sublist.trans h.queued⟩,
    (natreg 97 (by decide) (by decide) (by decide)).trans hpu, addr, frame, by omega⟩
  · exact (reg 163 (by decide) (by decide) (by decide) (by decide)).trans h.heads
  · exact (reg 164 (by decide) (by decide) (by decide) (by decide)).trans h.links
  · intro r
    have hd : A.d ≤ k := clockCoordinates_length_le A.I
    have hr := r.isLt
    have hh := site.header
    have hext : base + 4 ≤ extent A base := by unfold extent; omega
    exact ((frame.before _ (by omega) (by omega)).1).trans (h.coords r)

theorem pop_image {k : ℕ} (A : ClockCall k) (hk : 0 < k) (ε : ℝ) (base map params height W P : ℕ) (i : Fin A.d → ℕ)
    (S : MultiLayer A.d) (s : Store) (site : Site A base map params (2 ^ height) W) (hi : ∀ r, i r < A.q)
    (h : LayerImage A base map params (2 ^ height) W P i S s) (hne : S.queue ≠ []) :
    let u := picked A S
    ∃ t n, Run (multiInput A.I ε) (popLayer k A.d) s t n ∧ LayerImage A base map params (2 ^ height) W P i (pop A i S) t ∧
      RowFrame A base params i s t ∧ n ≤ A.d + 19 * Nat.clog 2 (2 * 2 ^ height) + 37 +
        (visitCost k A.d A.q (2 ^ height) + 6) * (outgoingIndices (lengthInstance A.I) A.I.graph.edges.length u).length := by
  let u := picked A S
  have hu : u ∈ incidentVertices A.I := h.queued.subset (picked_mem A S hne)
  obtain ⟨p, c, he, ph, hs, ha, hf, hc⟩ := extract_image A base map params height W P i S (multiInput A.I ε) s site hi h hne
  obtain ⟨t, n, ht, doneState, hrow, hn⟩ := relax_image A hk ε base map params (2 ^ height) W P u i (settle S u i) p site hi ph hu hs ha
  rw [← pop_of_nonempty A i S hne] at doneState
  exact ⟨t, c+n, Run.seq he ht, doneState, hf.trans hrow, by dsimp only [u] at hn; omega⟩

end NearLinearRSP.TwoResources.Supplement.LayerRAM

end

section

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace NearLinearRSP.TwoResources.Supplement.LayerRAM
open Mission.Structured Mission.Preprocess TableQuery

theorem queue_front {k : ℕ} (A : ClockCall k) (i : Fin A.d → ℕ) (S : MultiLayer A.d) (n : ℕ) :
    runQueue A i (n + 1) S = runQueue A i n (pop A i S) := by
  induction n with
  | zero => rw [runQueue_succ, runQueue_zero, runQueue_zero]
  | succ n ih => rw [runQueue_succ A i (n + 1), ih, runQueue_succ]

theorem linked_degree {k : ℕ} (I : MultiInstance k) (u : ℕ) :
    (outgoingIndices (lengthInstance I) I.graph.edges.length u).length = (outgoingEdges (lengthInstance I) u).length := by
  have h := congrArg List.length (outgoingIndices_edges (lengthInstance I) u)
  simp only [List.length_map, List.length_reverse] at h
  exact h

theorem layer_loop_run {k : ℕ} (A : ClockCall k) (hk : 0 < k) (ε : ℝ) (base map params height W P : ℕ)
    (i : Fin A.d → ℕ) (site : Site A base map params (2 ^ height) W) (hi : ∀ r, i r < A.q)
    (remaining : ℕ) (S : MultiLayer A.d) (s : Store) (h : LayerImage A base map params (2 ^ height) W P i S s)
    (hrem : S.queue.length = remaining) (hrank : S.nextRank + remaining = (incidentVertices A.I).length) :
    ∃ t n, Run (multiInput A.I ε) (layerLoop k A.d) s t n ∧
      LayerImage A base map params (2 ^ height) W P i (runQueue A i remaining S) t ∧ RowFrame A base params i s t ∧
      n ≤ vertexCost A.d (2 ^ height) * remaining +
        (visitCost k A.d A.q (2 ^ height) + 6) * outgoingWork (lengthInstance A.I) S.queue + 1 := by
  induction remaining generalizing S s with
  | zero =>
    have hg : (Guard.nat .lt 191 143).eval s = false := by
      simp only [Guard.eval, natTest, h.rank, h.graph.vertices.count_reg, Nat.add_zero] at hrank ⊢
      simp [hrank]
    exact ⟨s, 1, Run.loopFalse hg, h, fun _ _ _ => ⟨rfl,rfl⟩, by omega⟩
  | succ n ih =>
    have hne : S.queue ≠ [] := by intro he; simp [he] at hrem
    let u := picked A S
    let U := pop A i S
    have hpick : u ∈ S.queue := picked_mem A S hne
    have hU : U.queue = S.queue.erase u := by rw [show U = _ from pop_of_nonempty A i S hne, relaxAll_queue]; rfl
    have hRank : U.nextRank = S.nextRank + 1 := by rw [show U = _ from pop_of_nonempty A i S hne, relaxAll_nextRank]; rfl
    have hlen : U.queue.length = n := by rw [hU, List.length_erase_of_mem hpick, hrem]; omega
    have hg : (Guard.nat .lt 191 143).eval s = true := by
      simp only [Guard.eval, natTest, h.rank, h.graph.vertices.count_reg, decide_eq_true_eq]; omega
    obtain ⟨p,c,he,ph,frame,hc⟩ := pop_image A hk ε base map params height W P i S s site hi h hne
    obtain ⟨t,m,hr,doneState,hf,hm⟩ := ih U p ph hlen (by rw [hRank]; omega)
    have hwork := outgoingWork_erase (lengthInstance A.I) S.queue u hpick
    rw [← hU, ← linked_degree A.I u] at hwork
    let eCost := visitCost k A.d A.q (2 ^ height) + 6
    let vCost := vertexCost A.d (2 ^ height)
    have heq := congrArg (fun z => eCost * z) hwork
    simp only [Nat.mul_add] at heq
    change c ≤ A.d + 19 * Nat.clog 2 (2 * 2 ^ height) + 37 + eCost * (outgoingIndices (lengthInstance A.I) A.I.graph.edges.length u).length at hc
    change m ≤ vCost * n + eCost * outgoingWork (lengthInstance A.I) U.queue + 1 at hm
    rw [queue_front]
    refine ⟨t, _, Run.loopTrue hg he hr, doneState, frame.trans hf, ?_⟩
    change 1 + c + 1 + m ≤ vCost * (n + 1) + eCost * outgoingWork (lengthInstance A.I) S.queue + 1
    rw [Nat.mul_succ]
    have hv : vCost = A.d + 19 * Nat.clog 2 (2 * 2 ^ height) + 39 := rfl
    omega

end NearLinearRSP.TwoResources.Supplement.LayerRAM

end

section

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace NearLinearRSP.TwoResources.Supplement.LayerRAM
open Mission.Structured Mission.Preprocess TableQuery

theorem initialize_image {k : ℕ} (A : ClockCall k) (T : MultiTable A.d) (base map keys params B W P : ℕ)
    (i : Fin A.d → ℕ) (hd : 0 < A.d) (hi : ∀ r, i r < A.q) (input : RAMInput) (s : Store)
    (site : Site A base map params B W) (keyStart : map + 3 * A.I.graph.n + A.I.graph.edges.length ≤ keys)
    (keyEnd : keys + (incidentVertices A.I).length ≤ params) (hB : 0 < B) (hdis : W + 2 * B ≤ P)
    (h : RowInput A base map keys params B W P i T s) :
    ∃ t n, Run input (initializeRow A.d) s t n ∧ LayerImage A base map params B W P i (initializeLayer A T i) t ∧
      RowFrame A base keys i s t ∧
      n ≤ 15 * B + (14 * A.d + 33 + 19 * Nat.clog 2 (2 * B)) * (incidentVertices A.I).length + 16 := by
  let p := evalAtoms input beginRow s
  have hext := site.publicEnd
  have hW := site.workspace
  obtain ⟨hrow, ctl⟩ := row_ready A T base map keys params B W P i hi input s h
  obtain ⟨t, c, hr, heap, seed, nframe, rframe, hc⟩ := layer_heap_run A T base (map + A.I.graph.n) keys B W P i input hd hi
    (by omega) (by omega) hB site.capacity hdis (by omega) p hrow ctl.cfg
  obtain ⟨_, _, z, pre⟩ := begin_fields input s
  have control := ctl.transfer (fun a ha => hr.nat_frame a (control_start ha).2.2.2.2) (fun a ha hb => hr.real_frame a (start_real _ a ha hb))
  have high (a : ℕ) (ha : 101 ≤ a) (h191 : a ≠ 191) : t.nr a = s.nr a :=
    (hr.nat_frame a (start_nat _ a (by omega) (by omega) (by omega) (by omega) (by omega))).trans
      (pre a (by omega) (by omega) (by omega) h191)
  have tf : RowFrame A base keys i s t := by
    intro x hx hs
    exact ⟨nframe x (by omega) (fun v hv => by have := hs v hv; omega), rframe x hx⟩
  have gr := graph_transport A.I map s t h.graph (high 141 (by decide) (by decide)) (high 142 (by decide) (by decide))
    (high 143 (by decide) (by decide)) (fun x hl hh => (tf.after hi x (by omega) (by omega)).1)
  have numbers : Numbers A base T t := by
    intro v hv j hj
    have he := row_end A base v j hv hj
    obtain ⟨val, rank⟩ := h.numbers v hv j hj
    refine ⟨(rframe _ (by omega)).trans val, (nframe _ (by omega) ?_).trans rank⟩
    intro w hw
    have sep (y : ℕ) (hy : y < 2) : rowCell A base j v + 2 ≠ rowCell A base i w + y := by
      intro eq
      have ny := (separated_cell_fields A base j i v w 2 y (incident_valid _ _ hv) (incident_valid _ _ hw)
        hj hi (by omega) (by omega) eq).2.2
      omega
    exact ⟨by simpa only [Nat.add_zero] using sep 0 (by decide), sep 1 (by decide)⟩
  refine ⟨t, 4+c, Run.seq (run_atoms input beginRow s) hr, ⟨control, gr, (high 163 (by decide) (by decide)).trans h.heads,
    (high 164 (by decide) (by decide)).trans h.links, ?_, heap, (hr.nat_frame 191 (start_nat _ _ (by decide) (by decide)
      (by decide) (by decide) (by decide))).trans z, numbers, seed_parent_records A T base keys i t seed, List.Sublist.refl _⟩, tf, by omega⟩
  intro r
  have hh := site.header
  have hr' := r.isLt
  have hd' : A.d ≤ k := clockCoordinates_length_le A.I
  have he : base + 4 ≤ extent A base := by unfold extent; omega
  exact ((tf.before _ (by omega) (by omega)).1).trans (h.coords r)

theorem construct_layer_run {k : ℕ} (A : ClockCall k) (hk : 0 < k) (ε : ℝ) (T : MultiTable A.d)
    (base map keys params height W P : ℕ) (i : Fin A.d → ℕ) (hd : 0 < A.d) (hi : ∀ r, i r < A.q) (s : Store)
    (site : Site A base map params (2 ^ height) W) (keyStart : map + 3 * A.I.graph.n + A.I.graph.edges.length ≤ keys)
    (keyEnd : keys + (incidentVertices A.I).length ≤ params) (hdis : W + 2 * 2 ^ height ≤ P)
    (h : RowInput A base map keys params (2 ^ height) W P i T s) :
    let xs := incidentVertices A.I
    let U := runQueue A i xs.length (initializeLayer A T i)
    ∃ t n, Run (multiInput A.I ε) (runLayer k A.d) s t n ∧
      LayerImage A base map params (2 ^ height) W P i U t ∧ Numbers A base (constructLayer A T i) t ∧
      ParentRecords A base i (fun v => (constructLayer A T i v i).parent) t ∧ RowFrame A base keys i s t ∧
      n ≤ layerWork k A.d A.q (2 ^ height) xs.length A.I.graph.edges.length := by
  let xs := incidentVertices A.I
  let S := initializeLayer A T i
  let U := runQueue A i xs.length S
  obtain ⟨p,c,he,ph,pf,hc⟩ := initialize_image A T base map keys params (2 ^ height) W P i hd hi (multiInput A.I ε) s site
    keyStart keyEnd (by positivity) hdis h
  obtain ⟨t,m,hr,th,tf,hm⟩ := layer_loop_run A hk ε base map params height W P i site hi xs.length S p ph rfl (by simp [S, initializeLayer, xs])
  have hsyn := runQueue_parents A i xs.length S (initializeLayer_parents A T i) (incident_nodup A.I) (fun _ hh => hh)
  have empty : U.queue = [] := constructLayer_queue_empty A T i
  have hpar : ParentRecords A base i (fun v => (constructLayer A T i v i).parent) t := by
    intro v hv
    have hh : (constructLayer A T i v i).parent = U.parents v := hsyn.sync v hv (by change v ∉ U.queue; rw [empty]; simp)
    simpa only [hh] using th.parents v hv
  have cut : RowFrame A base keys i p t := fun x hx hs => tf x (by omega) hs
  have work : outgoingWork (lengthInstance A.I) S.queue = A.I.graph.edges.length := outgoingWork_active (lengthInstance A.I)
  rw [work] at hm
  refine ⟨t,c+m,Run.seq he hr,th,th.numbers,hpar,pf.trans cut,?_⟩
  change c ≤ 15 * _ + _ * xs.length + 16 at hc
  unfold layerWork
  rw [Nat.add_mul]
  dsimp only [xs] at hc hm
  omega

end NearLinearRSP.TwoResources.Supplement.LayerRAM

end

section

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace NearLinearRSP.TwoResources.Supplement.LayerRAM
open Mission.Structured TableQuery

theorem TableImage.update {k : ℕ} (A : ClockCall k) (base keys : ℕ) (T : MultiTable A.d) (i : Fin A.d → ℕ)
    (s t : Store) (hi : ∀ r, i r < A.q) (hkeys : extent A base ≤ keys) (h : TableImage A base T s)
    (hn : Numbers A base (constructLayer A T i) t) (hp : ParentRecords A base i (fun v => (constructLayer A T i v i).parent) t)
    (hf : RowFrame A base keys i s t) : TableImage A base (constructLayer A T i) t := by
  refine ⟨hn, ?_⟩
  intro j hj
  by_cases he : j = i
  · subst j; exact hp
  · intro v hv
    have eq := constructLayer_other_index A T i j v he
    obtain ⟨ht, hd, hg⟩ := h.parents j hj v hv
    have field (x : ℕ) (hx : x < A.d+4) := hf (rowCell A base j v + x)
      ((scanAddress_inside A base v (incident_valid A.I v hv) j hj x hx).trans_le hkeys)
      (outside_other_row A base i j v x hi hj hv hx he)
    simp only [eq]
    refine ⟨(by simpa only [Nat.add_zero] using (field 0 (by omega)).1.trans ht),
      ((field 1 (by omega)).1).trans hd, ?_⟩
    intro u hh r
    have hr := r.isLt
    have hfr := (field (4+r.val) (by omega)).2
    rw [← Nat.add_assoc] at hfr
    exact hfr.trans (hg u hh r)

theorem TableImage.frame {k : ℕ} {A : ClockCall k} {base : ℕ} {T : MultiTable A.d} {s t : Store}
    (h : TableImage A base T s) (hf : ∀ x < extent A base, t.nm x = s.nm x ∧ t.rm x = s.rm x) :
    TableImage A base T t := ⟨h.numbers.congr hf, fun j hj => (h.parents j hj).congr hj hf⟩

theorem TableImage.blank {k : ℕ} (A : ClockCall k) (base : ℕ) (s : Store)
    (hf : ∀ x, base + 4 ≤ x → x < extent A base → s.nm x = 0 ∧ s.rm x = 0) :
    TableImage A base (fun _ _ => ⟨1, .none, 0⟩) s := by
  have field (v : ℕ) (hv : v ∈ incidentVertices A.I) (i : Fin A.d → ℕ) (hi : ∀ r, i r < A.q) (x : ℕ) (hx : x < A.d + 4) :=
    hf (rowCell A base i v + x) (by unfold rowCell scanAddress; omega)
      (scanAddress_inside A base v (incident_valid A.I v hv) i hi x hx)
  constructor
  · intro v hv i hi
    exact ⟨by simpa only [Nat.add_zero, sub_self] using (field v hv i hi 0 (by omega)).2, (field v hv i hi 2 (by omega)).1⟩
  · intro i hi v hv
    exact ⟨by simpa only [Nat.add_zero, multiParentTag] using (field v hv i hi 0 (by omega)).1,
      (field v hv i hi 1 (by omega)).1, fun _ h => by contradiction⟩

theorem run_layer_preserves (k d a : ℕ) (ha : 101 ≤ a) (hb : a < EdgeRAM.bank k)
    (h191 : a ≠ 191) (h194 : a ≠ 194) : a ∉ (runLayer k d).natWrites := by
  have hs := start_nat d a (by omega) (by omega) (by omega) (by omega) (by omega)
  have hpop : a ∉ popCmd.natWrites := by
    have hm : ∀ j ∈ popCmd.natWrites, j < 100 := by decide
    exact fun hh => (Nat.not_lt_of_ge (by omega)) (hm _ hh)
  have copies := copies_preserve 99 97 (d+4) a (by omega)
  have hn := (visit_registers k d a hb).1 (by unfold StableNat; omega)
  simp [runLayer, initializeRow, beginRow, layerLoop, popLayer, extractVertex, settleCmd, settleOps, settledAddress,
    relaxNeighbors, firstNeighbor, scanNeighbors, advanceLink, Cmd.atoms, Cmd.natWrites, Atom.natWrites,
    hs, hpop, copies, hn, h191, h194]
  omega

theorem run_layer_high {k d n : ℕ} {input : RAMInput} {s t : Store} (h : Run input (runLayer k d) s t n) (a : ℕ)
    (ha : 101 ≤ a) (hb : a < EdgeRAM.bank k) (h191 : a ≠ 191) (h194 : a ≠ 194) : t.nr a = s.nr a :=
  h.nat_frame a (run_layer_preserves k d a ha hb h191 h194)

end NearLinearRSP.TwoResources.Supplement.LayerRAM

end

section

set_option autoImplicit false
set_option maxHeartbeats 1800000

namespace NearLinearRSP.TwoResources.Supplement.LayerRAM
open Mission.Structured TableQuery

theorem index_last {d : ℕ} (q : ℕ) (i : Fin (d + 1) → ℕ) :
    vectorIndex q i = vectorIndex q (Fin.init i) * q + i (Fin.last d) := by
  unfold vectorIndex
  rw [Fin.sum_univ_castSucc, Finset.sum_mul]
  simp only [Fin.val_last, Fin.val_castSucc, Nat.add_sub_cancel, Nat.sub_self, pow_zero, Nat.mul_one]
  congr 1
  apply Finset.sum_congr rfl
  intro r _
  have hr := r.isLt
  have he : d - r.val = d - 1 - r.val + 1 := by omega
  rw [he, pow_succ]
  simp [Fin.init, Nat.mul_assoc]

theorem divide_run (q digit remaining doneCount : ℕ) (input : RAMInput) (s : Store)
    (hpos : 0 < q) (hd : digit < q) (h1 : s.nr 31 = 1) (hq : s.nr 57 = q) (hl : s.nr 58 = q-1)
    (hv : s.nr 60 = remaining*q + digit) (hc : s.nr 61 = doneCount) :
    ∃ t, Run input divideLoop s t (4 * remaining + 1) ∧ t.nr 60 = digit ∧ t.nr 61 = doneCount + remaining := by
  induction remaining generalizing doneCount s with
  | zero =>
    have hg : (Guard.nat .lt 58 60).eval s = false := by simp [Guard.eval, natTest, hl, hv, show ¬q-1 < digit by omega]
    exact ⟨s, Run.loopFalse hg, by simpa using hv, by simpa using hc⟩
  | succ n ih =>
    let p := evalAtoms input divideBody s
    have hv' : p.nr 60 = n*q + digit := by
      simp [p, divideBody, evalAtoms, Atom.eval, Store.ofRAM, Store.at, ramStep, evalNat, hv, hq, Nat.succ_mul]
      omega
    have hc' : p.nr 61 = doneCount + 1 := by simp [p, divideBody, evalAtoms, Atom.eval, Store.ofRAM, Store.at, ramStep, evalNat, hc, h1]
    have hg : (Guard.nat .lt 58 60).eval s = true := by simp [Guard.eval, natTest, hl, hv, Nat.succ_mul]; omega
    obtain ⟨t, hr, h60, h61⟩ := ih (doneCount+1) p h1 hq hl hv' hc'
    have he := Run.loopTrue hg (run_atoms input divideBody s) hr
    have hw : 1 + divideBody.length + 1 + (4*n+1) = 4 * (n+1) + 1 := by change 1+2+1+_ = _; omega
    exact ⟨t, hw ▸ he, h60, by omega⟩

theorem digit_run (q n r val : ℕ) (input : RAMInput) (s : Store) (hq : 0 < q) (hv : val < q)
    (h1 : s.nr 31 = 1) (h57 : s.nr 57 = q) (h58 : s.nr 58 = q-1) (h60 : s.nr 60 = n*q + val) :
    ∃ t, Run input (digitCmd r) s t (4*n+4) ∧ t.nr 60 = n ∧ t.nr (stateReg r) = val ∧
      (∀ a, a ≠ 60 → a ≠ 61 → a ≠ stateReg r → t.nr a = s.nr a) ∧ t.rr = s.rr ∧ t.nm = s.nm ∧ t.rm = s.rm := by
  let p := digitZero.eval input s
  obtain ⟨w, hw, wr, wq⟩ := divide_run q val n 0 input p hq hv h1 h57 h58 h60 rfl
  have hr := Run.seq (Run.atom digitZero s) (Run.seq hw (run_atoms input (digitOps r) w))
  let t := evalAtoms input (digitOps r) w
  have hlarge := state_large r
  have he : 1 + (4*n+1+(digitOps r).length) = 4*n+4 := by change 1+(_+2)=_; omega
  have run : Run input (digitCmd r) s t (4*n+4) := he ▸ hr
  refine ⟨t, run, ?_, ?_, ?_, ?_, run.natMemory_frame rfl, run.realMemory_frame rfl⟩
  · simp [t,digitOps, evalAtoms, Atom.eval, Store.ofRAM, Store.at, ramStep, Function.update_of_ne (show 61 ≠ stateReg r by omega), wq]
  · simp [t,digitOps, evalAtoms, Atom.eval, Store.ofRAM, Store.at, ramStep, Function.update_of_ne (show stateReg r ≠ 60 by omega), wr]
  · intro a h0 h1 hs
    apply run.nat_frame
    simp [digitCmd, digitZero, divideLoop, divideBody, digitOps, Cmd.atoms, Cmd.natWrites, Atom.natWrites, h0, h1, hs]
  · funext a
    exact run.real_frame a (by change a ∉ (∅ : Finset ℕ); simp)

theorem digits_run (d q : ℕ) (i : Fin d → ℕ) (input : RAMInput) (s : Store) (hq : 0 < q) (hi : ∀ r, i r < q)
    (h1 : s.nr 31 = 1) (h57 : s.nr 57 = q) (h58 : s.nr 58 = q-1) (h60 : s.nr 60 = vectorIndex q i) :
    ∃ t c, Run input (digits d) s t c ∧ (∀ r : Fin d, t.nr (stateReg r.val) = i r) ∧
      (∀ a, a ≠ 60 → a ≠ 61 → (∀ r < d, a ≠ stateReg r) → t.nr a = s.nr a) ∧
      t.rr = s.rr ∧ t.nm = s.nm ∧ t.rm = s.rm ∧ c ≤ d * (4*q^d + 4) := by
  induction d generalizing s with
  | zero => exact ⟨s,0,Run.skip s,fun r => Fin.elim0 r,fun _ _ _ _ => rfl,rfl,rfl,rfl,by simp⟩
  | succ d ih =>
    let J := Fin.init i
    let n := vectorIndex q J
    have hj : ∀ r : Fin d, J r < q := fun r => hi r.castSucc
    obtain ⟨p, hp, pn, pd, pf, pr, pnm, prm⟩ := digit_run q n d (i (Fin.last d)) input s hq (hi _) h1 h57 h58 (h60.trans (index_last q i))
    have high := state_large d
    obtain ⟨t,c,hr,hval,hf,tr,tn,tm,hc⟩ := ih J p hj ((pf 31 (by decide) (by decide) (by omega)).trans h1)
      ((pf 57 (by decide) (by decide) (by omega)).trans h57) ((pf 58 (by decide) (by decide) (by omega)).trans h58) pn
    have hnum : n < q^d := vectorIndex_lt J hj
    have hpow : q^d ≤ q^(d+1) := Nat.pow_le_pow_right hq (by omega)
    have hm := Nat.mul_le_mul_left d (show 4*q^d+4 ≤ 4*q^(d+1)+4 by omega)
    refine ⟨t,_,Run.seq hp hr,?_,?_,tr.trans pr,tn.trans pnm,tm.trans prm,?_⟩
    · intro r
      refine Fin.lastCases ?_ (fun j => ?_) r
      · change t.nr (stateReg d) = i (Fin.last d)
        exact (hf _ (by omega) (by omega) (fun j hj he => by have := state_inj.mp he; omega)).trans pd
      · exact hval j
    · intro a h0 h1 hother
      exact (hf a h0 h1 (fun r h => hother r (by omega))).trans (pf a h0 h1 (hother d (by omega)))
    · rw [Nat.succ_mul d (4*q^(d+1)+4)]
      omega

end NearLinearRSP.TwoResources.Supplement.LayerRAM

end

section

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace NearLinearRSP.TwoResources.Supplement.LayerRAM
open Mission.Structured Mission.Preprocess TableQuery

def LayoutReg (d a : ℕ) : Prop := a ∈ [30,57,79,141,142,143,163,164,180,181,188,189,190,195] ∨ ∃ r < d, a = strideReg r

theorem TableContext.copy {k : ℕ} {A : ClockCall k} {base map keys params B W P : ℕ} {s t : Store}
    (h : TableContext A base map keys params B W P s) (hn : ∀ a, LayoutReg A.d a → t.nr a = s.nr a)
    (hr : t.rr = s.rr) (nm : t.nm = s.nm) : TableContext A base map keys params B W P t := by
  have g := graph_transport A.I map s t h.graph (hn 141 (by simp [LayoutReg])) (hn 142 (by simp [LayoutReg]))
    (hn 143 (by simp [LayoutReg])) (fun _ _ _ => congrFun nm _)
  exact ⟨⟨(hn 180 (by simp [LayoutReg])).trans h.cfg.winnerBase, (hn 181 (by simp [LayoutReg])).trans h.cfg.parentBase,
    (hn 188 (by simp [LayoutReg])).trans h.cfg.capacity⟩, g, (hn 163 (by simp [LayoutReg])).trans h.heads,
    (hn 164 (by simp [LayoutReg])).trans h.links, fun r => (congrFun nm _).trans (h.coords r), (congrFun nm _).trans h.source,
    (hn 189 (by simp [LayoutReg])).trans h.keysReg, (hn 190 (by simp [LayoutReg])).trans h.paramsReg,
    (hn 30 (by simp [LayoutReg])).trans h.zero, (hn 57 (by simp [LayoutReg])).trans h.q, (hn 79 (by simp [LayoutReg])).trans h.mode,
    (hn 195 (by simp [LayoutReg])).trans h.width, fun r => (hn _ (Or.inr ⟨r.val,r.isLt,rfl⟩)).trans (h.strides r),
    (congrFun hr _).trans h.limit, (congrFun hr _).trans h.denom, (congrFun hr _).trans h.threshold, (congrFun hr _).trans h.decay⟩

theorem TableContext.row_input {k : ℕ} {A : ClockCall k} {base map keys params B W P : ℕ}
    {T : MultiTable A.d} {i : Fin A.d → ℕ} {s : Store} (h : TableContext A base map keys params B W P s)
    (im : TableImage A base T s) (addr : s.nr 98 = rowCell A base i 0) (counts : ∀ r : Fin A.d, s.nr (stateReg r.val) = i r) :
    RowInput A base map keys params B W P i T s :=
  ⟨⟨h.cfg, h.zero, h.q, h.mode, addr, h.paramsReg, counts, h.strides, h.limit, h.denom, h.threshold, h.decay⟩,
    h.graph, h.heads, h.links, h.coords, h.keysReg, h.source, im.numbers⟩

theorem from_layer {k : ℕ} {A : ClockCall k} {base map keys params B W P : ℕ}
    {S : MultiLayer A.d} {i : Fin A.d → ℕ} {s : Store} (h : LayerImage A base map params B W P i S s)
    (keyReg : s.nr 189 = keys) (source : s.nm 1 = A.I.source) (width : s.nr 195 = (A.d+4)*A.I.graph.n) :
    TableContext A base map keys params B W P s :=
  ⟨h.control.cfg,h.graph,h.heads,h.links,h.coords,source,keyReg,h.control.parameters,h.control.zero,h.control.q,h.control.mode,
    width,h.control.strides,h.control.limit,h.control.denom,h.control.threshold,h.control.decay⟩

theorem TableFrame.trans {k : ℕ} {A : ClockCall k} {base lim : ℕ} {s p t : Store}
    (h : TableFrame A base lim s p) (g : TableFrame A base lim p t) : TableFrame A base lim s t := by
  intro x hx hs
  exact ⟨(g x hx hs).1.trans (h x hx hs).1,(g x hx hs).2.trans (h x hx hs).2⟩

theorem RowFrame.table {k : ℕ} {A : ClockCall k} {base lim : ℕ} {i : Fin A.d → ℕ} {s t : Store}
    (h : RowFrame A base lim i s t) (hi : ∀ r, i r < A.q) : TableFrame A base lim s t := by
  intro x hx hs
  exact hs.elim (fun hb => h.before x hx hb) (fun he => h.after hi x hx he)

end NearLinearRSP.TwoResources.Supplement.LayerRAM

end

section

set_option autoImplicit false
set_option maxHeartbeats 1800000

namespace NearLinearRSP.TwoResources.Supplement.LayerRAM
open Mission.Structured TableQuery

noncomputable def rowPosition {k : ℕ} (A : ClockCall k) (base j : ℕ) := base + 4 + ((A.d+4)*A.I.graph.n)*j

theorem position_index {k : ℕ} (A : ClockCall k) (base : ℕ) (i : Fin A.d → ℕ) :
    rowPosition A base (vectorIndex A.q i) = rowCell A base i 0 := by
  unfold rowPosition rowCell scanAddress
  ring

theorem layout_digits {d a : ℕ} (h : LayoutReg d a) :
    a ≠ 31 ∧ a ≠ 58 ∧ a ≠ 60 ∧ a ≠ 61 ∧ a ≠ 98 ∧ a ≠ 196 ∧ ∀ r, a ≠ stateReg r := by
  simp only [LayoutReg, List.mem_cons, List.not_mem_nil, or_false, stateReg, strideReg, CandidateRAM.current] at h ⊢
  rcases h with h | ⟨r, hr, h⟩ <;> refine ⟨by omega,by omega,by omega,by omega,by omega,by omega,fun _ => by omega⟩

theorem row_step_fields {k : ℕ} (A : ClockCall k) (base j : ℕ) (input : RAMInput) (s : Store)
    (hq : s.nr 57 = A.q) (hc : s.nr 196 = j + 1) (ha : s.nr 98 = rowPosition A base (j+1))
    (hw : s.nr 195 = (A.d+4)*A.I.graph.n) :
    let p := evalAtoms input rowStepOps s
    p.nr 196 = j ∧ p.nr 98 = rowPosition A base j ∧ p.nr 31 = 1 ∧ p.nr 60 = j ∧ p.nr 58 = A.q-1 ∧
      ∀ a, LayoutReg A.d a → p.nr a = s.nr a := by
  have he : rowPosition A base (j + 1) - (A.d+4)*A.I.graph.n = rowPosition A base j := by
    unfold rowPosition; rw [Nat.mul_succ]; omega
  simp only [rowStepOps, evalAtoms, Atom.eval, Store.ofRAM, Store.at, ramStep, evalNat, List.getElem?_cons_zero,
    Option.getD_some, Function.update_self, Function.update_of_ne (by decide : (196:ℕ) ≠ 31),
    Function.update_of_ne (by decide : (31:ℕ) ≠ 196)]
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  all_goals first
    | intro a hh
      obtain ⟨h31,h58,h60,_,h98,h196,_⟩ := layout_digits hh
      simp [Function.update_of_ne h31, Function.update_of_ne h58, Function.update_of_ne h60, Function.update_of_ne h98, Function.update_of_ne h196]
    | simp [hc, ha, hw, he, hq]

theorem step_row_run {k : ℕ} (A : ClockCall k) (hk : 0 < k) (ε : ℝ) (base map keys params height W P : ℕ)
    (i : Fin A.d → ℕ) (T : MultiTable A.d) (s : Store) (hq : 0 < A.q) (hd : 0 < A.d) (hi : ∀ r, i r < A.q)
    (site : Site A base map params (2^height) W) (keyStart : map + 3*A.I.graph.n + A.I.graph.edges.length ≤ keys)
    (keyEnd : keys + (incidentVertices A.I).length ≤ params) (hdis : W + 2*2^height ≤ P)
    (h : TableContext A base map keys params (2^height) W P s) (imageS : TableImage A base T s)
    (hcount : s.nr 196 = vectorIndex A.q i + 1) (haddr : s.nr 98 = rowPosition A base (vectorIndex A.q i + 1)) :
    ∃ t n, Run (multiInput A.I ε) (stepRow k A.d) s t n ∧ TableContext A base map keys params (2^height) W P t ∧
      TableImage A base (constructLayer A T i) t ∧ t.nr 196 = vectorIndex A.q i ∧ t.nr 98 = rowPosition A base (vectorIndex A.q i) ∧
      TableFrame A base keys s t ∧ n ≤ stepCost k A.d A.q (2^height) (incidentVertices A.I).length A.I.graph.edges.length := by
  let input := multiInput A.I ε
  let p := evalAtoms input rowStepOps s
  obtain ⟨idx,addr,one,val,limit,reg⟩ := row_step_fields A base _ input s h.q hcount haddr h.width
  have ph : TableContext A base map keys params (2^height) W P p := h.copy reg rfl rfl
  obtain ⟨w,c,he,counts,f,rr,nm,rm,hc⟩ := digits_run A.d A.q i input p hq hi one ph.q limit val
  have ctx := ph.copy (fun a ha => by
    obtain ⟨_,_,h60,h61,_,_,hs⟩ := layout_digits ha
    exact f a h60 h61 (fun r _ => hs r)) rr nm
  have img : TableImage A base T w := imageS.frame (fun _ _ => ⟨congrFun nm _,congrFun rm _⟩)
  have keep (r : ℕ) (h60 : r ≠ 60) (h61 : r ≠ 61) (hs : ∀ x, r ≠ stateReg x) :=
    f r h60 h61 (fun x _ => hs x)
  have wa : w.nr 98 = rowCell A base i 0 := (keep 98 (by decide) (by decide) (by intro x; unfold stateReg CandidateRAM.current; omega)).trans (addr.trans (position_index A base i))
  have wi : w.nr 196 = vectorIndex A.q i := (keep 196 (by decide) (by decide) (by intro x; unfold stateReg CandidateRAM.current; omega)).trans idx
  obtain ⟨t,m,hr,th,tn,tp,tf,hm⟩ := construct_layer_run A hk ε T base map keys params height W P i hd hi w site keyStart keyEnd hdis
    (ctx.row_input img wa counts)
  have high (a : ℕ) (ha : 101 ≤ a) (hb : a ≤ 200) (h191 : a ≠ 191) (h194 : a ≠ 194) := run_layer_high hr a ha (by unfold EdgeRAM.bank; omega) h191 h194
  have hext := site.publicEnd
  have he0 : base + 4 ≤ extent A base := by unfold extent; omega
  have hsource := ((tf.before 1 (by omega) (by omega)).1).trans ctx.source
  have tc := from_layer th ((high 189 (by decide) (by decide) (by decide) (by decide)).trans ctx.keysReg) hsource
    ((high 195 (by decide) (by decide) (by decide) (by decide)).trans ctx.width)
  have preFrame : TableFrame A base keys s w := fun _ _ _ => ⟨congrFun nm _,congrFun rm _⟩
  exact ⟨t,5+(c+m),Run.seq (run_atoms input rowStepOps s) (Run.seq he hr),tc,
    img.update A base keys T i w t hi (by omega) tn tp tf,
    (high 196 (by decide) (by decide) (by decide) (by decide)).trans wi, th.control.row.trans (position_index A base i).symm,
    preFrame.trans (tf.table hi), by unfold stepCost; omega⟩

end NearLinearRSP.TwoResources.Supplement.LayerRAM

end

section

set_option autoImplicit false
set_option maxHeartbeats 1700000

namespace NearLinearRSP.TwoResources.Supplement.LayerRAM
open Mission.Structured TableQuery

theorem rows_run {k : ℕ} (A : ClockCall k) (hk : 0 < k) (ε : ℝ) (base map keys params height W P : ℕ)
    (site : Site A base map params (2^height) W) (keyStart : map + 3*A.I.graph.n + A.I.graph.edges.length ≤ keys)
    (keyEnd : keys + (incidentVertices A.I).length ≤ params) (hdis : W + 2*2^height ≤ P) (hq : 0 < A.q) (hd : 0 < A.d)
    (rows : List (Fin A.d → ℕ)) (T : MultiTable A.d) (s : Store)
    (hvalid : ∀ i ∈ rows, ∀ r, i r < A.q) (codes : rows.map (vectorIndex A.q) = (List.range rows.length).reverse)
    (h : TableContext A base map keys params (2^height) W P s) (himage : TableImage A base T s)
    (hcount : s.nr 196 = rows.length) (haddr : s.nr 98 = rowPosition A base rows.length) :
    ∃ t n, Run (multiInput A.I ε) (tableLoop k A.d) s t n ∧ TableContext A base map keys params (2^height) W P t ∧
      TableImage A base (rows.foldl (constructLayer A) T) t ∧ TableFrame A base keys s t ∧
      n ≤ (stepCost k A.d A.q (2^height) (incidentVertices A.I).length A.I.graph.edges.length + 2) * rows.length + 1 := by
  induction rows generalizing T s with
  | nil =>
    have hg : (Guard.nat .lt 30 196).eval s = false := by simp [Guard.eval,natTest,h.zero,hcount]
    exact ⟨s,1,Run.loopFalse hg,h,himage,fun _ _ _ => ⟨rfl,rfl⟩,by simp⟩
  | cons i rows ih =>
    have pair : vectorIndex A.q i = rows.length ∧ rows.map (vectorIndex A.q) = (List.range rows.length).reverse := by
      simpa only [List.map_cons,List.length_cons,List.range_succ,List.reverse_append,List.reverse_singleton,
        List.singleton_append,List.cons.injEq] using codes
    have hi := hvalid i (by simp)
    have hg : (Guard.nat .lt 30 196).eval s = true := by simp [Guard.eval,natTest,h.zero,hcount]
    obtain ⟨p,c,hp,ctx,imageP,pc,pa,hf,hc⟩ := step_row_run A hk ε base map keys params height W P i T s hq hd hi site
      keyStart keyEnd hdis h himage (by simpa only [pair.1,List.length_cons] using hcount)
      (by simpa only [pair.1,List.length_cons] using haddr)
    obtain ⟨t,m,hr,doneState,imageT,gt,hm⟩ := ih (constructLayer A T i) p (fun j hj => hvalid j (List.mem_cons_of_mem _ hj)) pair.2
      ctx imageP (pc.trans pair.1) (pa.trans (congrArg (rowPosition A base) pair.1))
    refine ⟨t,_,Run.loopTrue hg hp hr,doneState,imageT,hf.trans gt,?_⟩
    rw [List.length_cons,Nat.mul_succ]; omega

theorem table_loop_run {k : ℕ} (A : ClockCall k) (hk : 0 < k) (ε : ℝ) (base map keys params height W P : ℕ)
    (site : Site A base map params (2^height) W) (keyStart : map + 3*A.I.graph.n + A.I.graph.edges.length ≤ keys)
    (keyEnd : keys + (incidentVertices A.I).length ≤ params) (hdis : W + 2*2^height ≤ P) (hq : 0 < A.q) (hd : 0 < A.d)
    (s : Store) (h : TableContext A base map keys params (2^height) W P s)
    (himage : TableImage A base (fun _ _ => ⟨1,.none,0⟩) s) (hcount : s.nr 196 = A.q^A.d) (haddr : s.nr 98 = extent A base) :
    ∃ t n, Run (multiInput A.I ε) (tableLoop k A.d) s t n ∧ TableContext A base map keys params (2^height) W P t ∧
      TableImage A base (constructTable A) t ∧ TableFrame A base keys s t ∧
      n ≤ (stepCost k A.d A.q (2^height) (incidentVertices A.I).length A.I.graph.edges.length + 2) * A.q^A.d + 1 := by
  let rs := (vectors A.d A.q).reverse
  have hl : rs.length = A.q^A.d := by
    have h := congrArg List.length (vectorIndices_in_order A.d A.q)
    simpa only [rs,List.length_reverse,List.length_map,List.length_range] using h
  have codes : rs.map (vectorIndex A.q) = (List.range rs.length).reverse := by
    rw [hl,← vectorIndices_in_order A.d A.q,List.map_reverse]
  have hv (i : Fin A.d → ℕ) (hm : i ∈ rs) : ∀ r, i r < A.q := (mem_vectors i).mp (List.mem_reverse.mp hm)
  have pos : rowPosition A base rs.length = extent A base := by rw [hl]; rfl
  obtain ⟨t,n,hr,ctx,im,f,hc⟩ := rows_run A hk ε base map keys params height W P site keyStart keyEnd hdis hq hd
    rs _ s hv codes h himage (hcount.trans hl.symm) (haddr.trans pos.symm)
  exact ⟨t,n,hr,ctx,im,f,hl ▸ hc⟩

end NearLinearRSP.TwoResources.Supplement.LayerRAM

end

section

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace NearLinearRSP.TwoResources.Supplement.LayerRAM
open Mission.Structured TableQuery

theorem volume_run (d : ℕ) (input : RAMInput) (s : Store) :
    ∃ t, Run input (volumeCmd d) s t (d*(4*s.nr 57+5)+3) ∧ t.nr 196 = (s.nr 57)^d ∧
      (∀ a, 70 ≤ a → a ≠ 196 → (∀ r<d, a ≠ strideReg r) → t.nr a = s.nr a) ∧
      t.rr = s.rr ∧ t.nm = s.nm ∧ t.rm = s.rm := by
  let p := evalAtoms input volumeOps s
  have one : p.nr 31 = 1 := rfl
  have unit : p.nr 58 = 1 := rfl
  have q : p.nr 57 = s.nr 57 := rfl
  obtain ⟨v,hr,hvol,_,hregs,rr,nm,rm⟩ := powers_run input p d one
  rw [unit,q,one_mul] at hvol
  rw [q] at hr
  let t := saveVolume.eval input v
  have cost : 2+(d*(4*s.nr 57+5)+1) = d*(4*s.nr 57+5)+3 := by omega
  refine ⟨t,cost ▸ Run.seq (run_atoms input volumeOps s) (Run.seq hr (Run.atom saveVolume v)),hvol,?_,rr,nm,rm⟩
  intro a ha h196 hstr
  have h := hregs a hstr (by omega) (by omega) (by omega)
  have hp : p.nr a = s.nr a := by
    simp [p,volumeOps,evalAtoms,Atom.eval,Store.ofRAM,Store.at,ramStep,Function.update_of_ne (show a ≠ 31 by omega),
      Function.update_of_ne (show a ≠ 58 by omega)]
  exact (Function.update_of_ne h196 _ _).trans (h.trans hp)

theorem shape_extra (k d : ℕ) (input : RAMInput) (s : Store) :
    let p := SpaceRAM.shaped k d input s
    p.nr 60 = s.nm 2 ∧ p.rr = s.rr ∧ ∀ a, 70 ≤ a → p.nr a = s.nr a := by
  dsimp only
  refine ⟨?_,rfl,?_⟩
  · simp [SpaceRAM.shaped,added,SpaceRAM.shapeOps,evalAtoms,Atom.eval,Store.ofRAM,Store.at,ramStep]
  · intro a ha
    simp [SpaceRAM.shaped,added,SpaceRAM.shapeOps,evalAtoms,Atom.eval,Store.ofRAM,Store.at,ramStep,
      Function.update_of_ne (show a ≠ 49 by omega),Function.update_of_ne (show a ≠ 58 by omega),
      Function.update_of_ne (show a ≠ 31 by omega),Function.update_of_ne (show a ≠ 60 by omega),
      Function.update_of_ne (show a ≠ 57 by omega),Function.update_of_ne (show a ≠ 65 by omega),
      Function.update_of_ne (show a ≠ 30 by omega)]

structure GridRegisters {k : ℕ} (A : ClockCall k) (base map : ℕ) (s : Store) : Prop where
  start : s.nr 98 = extent A base
  count : s.nr 196 = A.q^A.d
  width : s.nr 195 = (A.d+4)*A.I.graph.n
  zero : s.nr 30 = 0
  q : s.nr 57 = A.q
  heads : s.nr 163 = map + 2*A.I.graph.n
  links : s.nr 164 = map + 3*A.I.graph.n
  strides : ∀ j : Fin A.d, s.nr (strideReg j.val) = stride A.I.graph.n A.q j

theorem grid_setup_run {k : ℕ} (A : ClockCall k) (base map : ℕ) (input : RAMInput) (s : Store)
    (qreg : s.nr 57 = A.q) (qmem : s.nm 0 = A.q) (nodes : s.nm 2 = A.I.graph.n)
    (baseReg : s.nr 200 = base) (mapReg : s.nr 141 = map) :
    ∃ t, Run input (gridSetup k A.d) s t (2*(A.d*(4*A.q+5))+A.d+30) ∧ GridRegisters A base map t ∧
      (∀ a, GridFixed a → t.nr a = s.nr a) ∧ t.rr = s.rr ∧ t.nm = s.nm ∧ t.rm = s.rm := by
  obtain ⟨p,hp,cnt,preg,pr,pn,pm⟩ := volume_run A.d input s
  rw [qreg] at cnt hp
  let v := SpaceRAM.shaped k A.d input p
  obtain ⟨hv,width,q,_,one,vn,vm⟩ := SpaceRAM.shape_run k A.d input p
  obtain ⟨nodesV,vr,vreg⟩ := shape_extra k A.d input p
  change v.nr 58 = _ at width
  change v.nr 57 = _ at q
  change v.nr 60 = _ at nodesV
  rw [pn,nodes] at width nodesV
  rw [pn,qmem] at q
  let w := saveWidth.eval input v
  have wq : w.nr 57 = A.q := q
  have wwidth : w.nr 58 = (A.d+4)*A.I.graph.n := width
  obtain ⟨y,hy,vol,str,regs,yr,yn,ym⟩ := powers_run input w A.d one
  rw [wq] at hy
  rw [wq,wwidth] at vol str
  have vkeep (a : ℕ) (ha : 70 ≤ a) (h196 : a ≠ 196) (hstr : ∀ r, a ≠ strideReg r) : v.nr a = s.nr a :=
    (vreg _ ha).trans (preg _ ha h196 (fun r _ => hstr r))
  have ykeep (a : ℕ) (ha : 70 ≤ a) (hstr : ∀ r, a ≠ strideReg r) : y.nr a = w.nr a :=
    regs _ (fun r _ => hstr r) (by omega) (by omega) (by omega)
  have same (a : ℕ) (ha : 70 ≤ a) (h195 : a ≠ 195) (h196 : a ≠ 196) (hstr : ∀ r, a ≠ strideReg r) : y.nr a = s.nr a :=
    (ykeep a ha hstr).trans ((Function.update_of_ne h195 _ _).trans (vkeep a ha h196 hstr))
  have y195 : y.nr 195 = (A.d+4)*A.I.graph.n := (ykeep _ (by decide) (by intro r; unfold strideReg CandidateRAM.current; omega)).trans width
  have y196 : y.nr 196 = A.q^A.d := (ykeep _ (by decide) (by intro r; unfold strideReg CandidateRAM.current; omega)).trans ((vreg 196 (by decide)).trans cnt)
  have y200 : y.nr 200 = base := (same _ (by decide) (by decide) (by decide) (by intro r; unfold strideReg CandidateRAM.current; omega)).trans baseReg
  have y141 : y.nr 141 = map := (same _ (by decide) (by decide) (by decide) (by intro r; unfold strideReg CandidateRAM.current; omega)).trans mapReg
  have low (a : ℕ) (ha : a < 98) (h58 : a ≠ 58) (h61 : a ≠ 61) (h62 : a ≠ 62) :=
    regs a (fun r _ => by have := stride_large r; omega) h58 h61 h62
  have y60 : y.nr 60 = A.I.graph.n := (low 60 (by decide) (by decide) (by decide) (by decide)).trans nodesV
  have y57 : y.nr 57 = A.q := (low 57 (by decide) (by decide) (by decide) (by decide)).trans wq
  let t := evalAtoms input gridRegs y
  have fields : GridRegisters A base map t := by
    constructor
    all_goals first
      | intro j
        have h98 : strideReg j.val ≠ 98 := by unfold strideReg CandidateRAM.current; omega
        have h163 : strideReg j.val ≠ 163 := by unfold strideReg CandidateRAM.current; omega
        have h164 : strideReg j.val ≠ 164 := by unfold strideReg CandidateRAM.current; omega
        have hlarge := stride_large j.val
        simpa [t,gridRegs,evalAtoms,Atom.eval,Store.ofRAM,Store.at,ramStep,stride,
          Function.update_of_ne h98,Function.update_of_ne h163,Function.update_of_ne h164,
          Function.update_of_ne (show strideReg j.val ≠ 30 by omega),Function.update_of_ne (show strideReg j.val ≠ 65 by omega)] using str j.val j.isLt
      | simp [t,gridRegs,evalAtoms,Atom.eval,Store.ofRAM,Store.at,ramStep,evalNat,
          y195,y196,y200,y141,y60,y57,vol,extent] <;> omega
  have cost : (A.d*(4*A.q+5)+3)+(A.d+19+(1+(A.d*(4*A.q+5)+gridRegs.length))) = 2*(A.d*(4*A.q+5))+A.d+30 := by
    change _+(_+(1+(_+7)))=_; omega
  refine ⟨t,cost ▸ Run.seq hp (Run.seq hv (Run.seq (Run.atom saveWidth v) (Run.seq hy (run_atoms input gridRegs y)))),
    fields,?_,yr.trans (vr.trans pr),yn.trans (vn.trans pn),ym.trans (vm.trans pm)⟩
  intro a hh
  obtain ⟨ha,h98,h163,h164,h195,h196,hstr⟩ := hh
  simpa [t,gridRegs,evalAtoms,Atom.eval,Store.ofRAM,Store.at,ramStep,Function.update_of_ne h98,Function.update_of_ne h163,
    Function.update_of_ne h164,Function.update_of_ne (show a ≠ 30 by omega),Function.update_of_ne (show a ≠ 65 by omega)] using same a ha h195 h196 hstr

end NearLinearRSP.TwoResources.Supplement.LayerRAM

end

section

set_option autoImplicit false
set_option maxHeartbeats 1800000

namespace NearLinearRSP.TwoResources.Supplement.LayerRAM
open Mission.Structured TableQuery

theorem digits_preserve (d a : ℕ) (ha : 101 ≤ a) (hs : ∀ r, a ≠ stateReg r) : a ∉ (digits d).natWrites := by
  induction d with
  | zero => simp [digits,Cmd.natWrites]
  | succ d ih =>
    simp [digits,digitCmd,digitZero,divideLoop,divideBody,digitOps,Cmd.atoms,Cmd.natWrites,Atom.natWrites,ih,hs d]
    omega

theorem loop_outer {k d n : ℕ} {input : RAMInput} {s t : Store} (h : Run input (tableLoop k d) s t n)
    (a : ℕ) (hh : TableOuter k a) : t.nr a = s.nr a := by
  obtain ⟨ha,hb,h191,h194,h196,st⟩ := hh
  apply h.nat_frame
  have hl := run_layer_preserves k d a ha hb h191 h194
  have hd := digits_preserve d a ha st
  simp [tableLoop,stepRow,rowStepOps,Cmd.atoms,Cmd.natWrites,Atom.natWrites,hl,hd,h196]
  omega

theorem build_table_run {k : ℕ} (A : ClockCall k) (hk : 0 < k) (ε : ℝ) (base map keys params height W P : ℕ)
    (site : Site A base map params (2^height) W) (keyStart : map+3*A.I.graph.n+A.I.graph.edges.length ≤ keys)
    (keyEnd : keys + (incidentVertices A.I).length ≤ params) (hdis : W + 2*2^height ≤ P) (hq : 0 < A.q) (hd : 0 < A.d)
    (s : Store) (h : TableInput A base map keys params (2^height) W P s)
    (blank : ∀ x, base+4 ≤ x → x < extent A base → s.nm x = 0 ∧ s.rm x = 0) :
    ∃ t n, Run (multiInput A.I ε) (buildTableCmd k A.d) s t n ∧ TableContext A base map keys params (2^height) W P t ∧
      TableImage A base (constructTable A) t ∧ TableFrame A base keys s t ∧ t.nr 203 = extent A base ∧
      (∀ a, TableOuter k a → GridFixed a → a ≠ 203 → t.nr a = s.nr a) ∧
      n ≤ tableCost k A.d A.q (2^height) (incidentVertices A.I).length A.I.graph.edges.length := by
  let input := multiInput A.I ε
  obtain ⟨p,hr,gr,reg,rr,nm,rm⟩ := grid_setup_run A base map input s h.clocks.q h.q h.nodes h.address h.graph.vertices.base_reg
  let w := saveEnd.eval input p
  have endReg : w.nr 203 = extent A base := gr.start
  have keep (a : ℕ) (ha : a ≠ 203) : w.nr a = p.nr a := Function.update_of_ne ha _ _
  have fix (a : ℕ) (ha : a ≠ 203) (hf : GridFixed a) := (keep a ha).trans (reg a hf)
  have g (a : ℕ) (ha : a ∈ [79,141,142,143,180,181,188,189,190]) : GridFixed a := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    unfold GridFixed
    refine ⟨by omega,by omega,by omega,by omega,by omega,by omega,?_⟩
    intro r; unfold strideReg CandidateRAM.current; omega
  have graph := graph_transport A.I map s w h.graph (fix 141 (by decide) (g _ (by decide))) (fix 142 (by decide) (g _ (by decide)))
    (fix 143 (by decide) (g _ (by decide))) (fun _ _ _ => congrFun nm _)
  have ctx : TableContext A base map keys params (2^height) W P w :=
    ⟨⟨(fix 180 (by decide) (g _ (by decide))).trans h.cfg.winnerBase,(fix 181 (by decide) (g _ (by decide))).trans h.cfg.parentBase,
      (fix 188 (by decide) (g _ (by decide))).trans h.cfg.capacity⟩,graph,gr.heads,gr.links,
      fun r => (congrFun nm _).trans (h.coords r),(congrFun nm _).trans h.source,
      (fix 189 (by decide) (g _ (by decide))).trans h.keys,(fix 190 (by decide) (g _ (by decide))).trans h.params,gr.zero,gr.q,
      (fix 79 (by decide) (g _ (by decide))).trans h.clocks.zeroOnly,gr.width,
      fun r => (keep _ (by unfold strideReg CandidateRAM.current; omega)).trans (gr.strides r),
      (congrFun rr _).trans h.clocks.limit,(congrFun rr _).trans h.clocks.denominator,
      (congrFun rr _).trans h.clocks.threshold,(congrFun rr _).trans h.clocks.decay⟩
  have im : TableImage A base (fun _ _ => ⟨1,.none,0⟩) w :=
    (TableImage.blank A base s blank).frame (fun _ _ => ⟨congrFun nm _,congrFun rm _⟩)
  obtain ⟨t,c,he,ct,table,frame,hc⟩ := table_loop_run A hk ε base map keys params height W P site keyStart keyEnd hdis hq hd w ctx im gr.count gr.start
  have h203 : TableOuter k 203 := by
    refine ⟨by decide,by unfold EdgeRAM.bank; omega,by decide,by decide,by decide,?_⟩
    intro r; unfold stateReg CandidateRAM.current; omega
  have hf : TableFrame A base keys s w := fun _ _ _ => ⟨congrFun nm _,congrFun rm _⟩
  exact ⟨t,_,Run.seq hr (Run.seq (Run.atom saveEnd p) he),ct,table,hf.trans frame,(loop_outer he 203 h203).trans endReg,
    fun a ho hg hh => (loop_outer he a ho).trans (fix a hh hg),by unfold tableCost; omega⟩

end NearLinearRSP.TwoResources.Supplement.LayerRAM

end

open NearLinearRSP.TwoResources NearLinearRSP.TwoResources.Supplement
open NearLinearRSP.TwoResources.Mission.Structured NearLinearRSP.TwoResources.Supplement.LayerRAM NearLinearRSP.TwoResources.Supplement.TableQuery

theorem solution {k : ℕ} (A : ClockCall k) (hk : 0 < k) (ε : ℝ) (base map keys params height W P : ℕ)
    (site : Site A base map params (2^height) W) (keyStart : map+3*A.I.graph.n+A.I.graph.edges.length ≤ keys)
    (keyEnd : keys + (incidentVertices A.I).length ≤ params) (hdis : W + 2*2^height ≤ P) (hq : 0 < A.q) (hd : 0 < A.d)
    (s : Store) (h : TableInput A base map keys params (2^height) W P s)
    (blank : ∀ x, base+4 ≤ x → x < extent A base → s.nm x = 0 ∧ s.rm x = 0) :
    ∃ t n, Run (multiInput A.I ε) (buildTableCmd k A.d) s t n ∧ TableContext A base map keys params (2^height) W P t ∧
      TableImage A base (constructTable A) t ∧ TableFrame A base keys s t ∧ t.nr 203 = extent A base ∧
      (∀ a, TableOuter k a → GridFixed a → a ≠ 203 → t.nr a = s.nr a) ∧
      n ≤ tableCost k A.d A.q (2^height) (incidentVertices A.I).length A.I.graph.edges.length :=
  LayerRAM.build_table_run A hk ε base map keys params height W P site keyStart keyEnd hdis hq hd s h blank
