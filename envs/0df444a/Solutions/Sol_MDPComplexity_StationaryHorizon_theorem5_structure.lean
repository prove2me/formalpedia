-- Prove2me | solution 1 for MDPComplexity.StationaryHorizon.theorem5_structure
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-24T00:53:03.434527+00:00
-- url     : https://prove2.me/submissions/7dade5c5-7fdb-4999-a319-9aa9a370382f

import Mathlib
import Definitions.Def_MDPComplexity_StationaryHorizon_Model



open MDPComplexity.StationaryHorizon
namespace MDPProof
variable {S : Type} [Fintype S]

inductive Path (M : DetMDP S) : S → S → Type
  | nil (s : S) : Path M s s
  | cons {s t : S} (d : M.D s) (p : Path M (M.next s d) t) : Path M s t

namespace Path
variable {M : DetMDP S} {s t u : S}
def length : {s t : S} → Path M s t → ℕ
  | _, _, .nil _ => 0
  | _, _, .cons _ p => p.length + 1

def cost : {s t : S} → Path M s t → ℝ
  | _, _, .nil _ => 0
  | _, _, .cons d p => M.c _ d + p.cost

def arcs : {s t : S} → Path M s t → List (Σ s, M.D s)
  | _, _, .nil _ => []
  | _, _, .cons d p => ⟨_, d⟩ :: p.arcs

def vertices : {s t : S} → Path M s t → List S
  | _, _, .nil s => [s]
  | _, _, .cons (s := s) _ p => s :: p.vertices

def append : {s t u : S} → Path M s t → Path M t u → Path M s u
  | _, _, _, .nil _, q => q
  | _, _, _, .cons d p, q => .cons d (p.append q)

@[simp] theorem length_append (p : Path M s t) (q : Path M t u) :
    (p.append q).length = p.length + q.length := by
  induction p with
  | nil => simp [append, length]
  | cons d p ih => simp [append, length, ih, Nat.add_comm, Nat.add_left_comm]

@[simp] theorem cost_append (p : Path M s t) (q : Path M t u) :
    (p.append q).cost = p.cost + q.cost := by
  induction p with
  | nil => simp [append, cost]
  | cons d p ih => simp [append, cost, ih, add_assoc]

@[simp] theorem arcs_append (p : Path M s t) (q : Path M t u) :
    (p.append q).arcs = p.arcs ++ q.arcs := by
  induction p with
  | nil => rfl
  | cons d p ih => simp [append, arcs, ih]

def sources : {s t : S} → Path M s t → List S
  | _, _, .nil _ => []
  | s, _, .cons _ p => s :: p.sources

@[simp] theorem sources_append (p : Path M s t) (q : Path M t u) :
    (p.append q).sources = p.sources ++ q.sources := by
  induction p with
  | nil => rfl
  | cons d p ih => simp [append, sources, ih]

@[simp] theorem vertices_eq (p : Path M s t) : p.vertices = p.sources ++ [t] := by
  induction p with
  | nil => rfl
  | cons d p ih => simp [vertices, sources, ih]

@[simp] theorem sources_length (p : Path M s t) : p.sources.length = p.length := by
  induction p with
  | nil => rfl
  | cons d p ih => simp [sources, length, ih]

@[simp] theorem source_mem (p : Path M s t) : s ∈ p.vertices := by
  cases p <;> simp [vertices]

@[simp] theorem target_mem (p : Path M s t) : t ∈ p.vertices := by
  rw [vertices_eq]
  simp

@[simp] theorem vertices_append (p : Path M s t) (q : Path M t u) :
    (p.append q).vertices = p.sources ++ q.vertices := by
  rw [vertices_eq, sources_append, vertices_eq, List.append_assoc]

theorem split_vertex (p : Path M s t) {v : S} (hv : v ∈ p.vertices) :
    ∃ a : Path M s v, ∃ b : Path M v t, p = a.append b := by
  induction p with
  | nil s =>
    have h : v = s := by simpa [vertices] using hv
    subst v
    exact ⟨.nil s, .nil s, rfl⟩
  | @cons s t d p ih =>
    have h : v = s ∨ v ∈ p.vertices := by simpa [vertices] using hv
    rcases h with h | h
    · subst v
      exact ⟨.nil _, .cons d p, rfl⟩
    · obtain ⟨a, b, hab⟩ := ih h
      subst p
      exact ⟨.cons d a, b, rfl⟩

theorem arc_endpoints (p : Path M s t) (a : Σ s, M.D s) (ha : a ∈ p.arcs) :
    a.1 ∈ p.vertices ∧ M.next a.1 a.2 ∈ p.vertices := by
  induction p with
  | nil => simp [arcs] at ha
  | cons d p ih =>
    rcases List.mem_cons.mp ha with h | h
    · subst a
      exact ⟨List.mem_cons_self, List.mem_cons_of_mem _ (source_mem p)⟩
    · exact ⟨List.mem_cons_of_mem _ (ih h).1, List.mem_cons_of_mem _ (ih h).2⟩

theorem start_mem_sources (p : Path M s t) (h : 0 < p.length) : s ∈ p.sources := by
  cases p with
  | nil => simp [length] at h
  | cons => exact List.mem_cons_self

theorem mem_vertices_append (p : Path M s t) (q : Path M t u) (v : S) :
    v ∈ (p.append q).vertices ↔ v ∈ p.vertices ∨ v ∈ q.vertices := by
  rw [vertices_append, vertices_eq p]
  simp only [List.mem_append, List.mem_singleton]
  constructor
  · rintro (h | h)
    · exact Or.inl (Or.inl h)
    · exact Or.inr h
  · rintro ((h | rfl) | h)
    · exact Or.inl h
    · exact Or.inr (source_mem q)
    · exact Or.inr h
end Path

def prepend {M : DetMDP S} {l : ℕ} (s : S) (d : M.D s) (W : M.Walk l)
    (h : W.x 0 = M.next s d) : M.Walk (l + 1) where
  x := Fin.cons s W.x
  e := by
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact d
    · exact W.e j
  valid := by
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact h.symm
    · exact W.valid j

@[simp] theorem cost_prepend {M : DetMDP S} {l : ℕ} (s : S) (d : M.D s)
    (W : M.Walk l) (h : W.x 0 = M.next s d) :
    (prepend s d W h).cost = M.c s d + W.cost := by
  unfold DetMDP.Walk.cost
  rw [Fin.sum_univ_succ]
  rfl

def tail {M : DetMDP S} {l : ℕ} (W : M.Walk (l + 1)) : M.Walk l where
  x := fun i => W.x i.succ
  e := fun i => W.e i.succ
  valid := fun i => W.valid i.succ

@[simp] theorem cost_tail {M : DetMDP S} {l : ℕ} (W : M.Walk (l + 1)) :
    W.cost = M.c (W.x 0) (W.e 0) + (tail W).cost := by
  unfold DetMDP.Walk.cost
  rw [Fin.sum_univ_succ]
  rfl

namespace Path
variable {M : DetMDP S}
def realize : {s t : S} → (p : Path M s t) →
    {W : M.Walk p.length // W.x 0 = s ∧ W.x ⟨p.length, Nat.lt_succ_self _⟩ = t}
  | _, _, .nil s =>
    ⟨{ x := fun _ => s
       e := fun i => Fin.elim0 i
       valid := fun i => Fin.elim0 i }, rfl, rfl⟩
  | s, _, .cons d p =>
    let q := p.realize
    ⟨prepend s d q.val q.property.1, rfl, q.property.2⟩

@[simp] theorem realize_cost {s t : S} (p : Path M s t) : p.realize.val.cost = p.cost := by
  induction p with
  | nil s =>
    change (∑ i : Fin 0, M.c s (Fin.elim0 i)) = 0
    simp
  | cons d p ih =>
    change (prepend _ d p.realize.val p.realize.property.1).cost = M.c _ d + p.cost
    rw [cost_prepend, ih]

@[simp] theorem realize_vertices {s t : S} (p : Path M s t) :
    List.ofFn p.realize.val.x = p.vertices := by
  induction p with
  | nil s => simp [realize, vertices, length, List.ofFn_succ]
  | cons d p ih =>
    rw [List.ofFn_succ]
    change _ :: List.ofFn p.realize.val.x = _ :: p.vertices
    exact congrArg (List.cons _) ih

@[simp] theorem realize_sources {s t : S} (p : Path M s t) :
    List.ofFn (fun i => p.realize.val.x i.castSucc) = p.sources := by
  induction p with
  | nil s => rfl
  | cons d p ih =>
    change List.ofFn (fun i : Fin (p.length + 1) => (prepend _ d p.realize.val p.realize.property.1).x i.castSucc) = _
    rw [List.ofFn_succ]
    change _ :: List.ofFn (fun i => p.realize.val.x i.castSucc) = _ :: p.sources
    exact congrArg (List.cons _) ih

@[simp] theorem realize_arcs_list {s t : S} (p : Path M s t) :
    List.ofFn (fun i => (⟨p.realize.val.x i.castSucc, p.realize.val.e i⟩ : Σ s, M.D s)) = p.arcs := by
  induction p with
  | nil s => rfl
  | cons d p ih =>
    change List.ofFn (fun i : Fin (p.length + 1) => (⟨(prepend _ d p.realize.val p.realize.property.1).x i.castSucc, (prepend _ d p.realize.val p.realize.property.1).e i⟩ : Σ s, M.D s)) = _
    rw [List.ofFn_succ]
    change _ :: List.ofFn (fun i => (⟨p.realize.val.x i.castSucc, p.realize.val.e i⟩ : Σ s, M.D s)) = _ :: p.arcs
    exact congrArg (List.cons _) ih

@[simp] theorem realize_arcs {s t : S} (p : Path M s t) :
    p.realize.val.arcs = (p.arcs : Multiset (Σ s, M.D s)) := by
  unfold DetMDP.Walk.arcs
  rw [realize_arcs_list]

theorem realize_simple {s t : S} (p : Path M s t) (h : p.vertices.Nodup) :
    p.realize.val.IsSimplePath := by
  apply List.nodup_ofFn.mp
  rwa [realize_vertices]

theorem realize_cycle {s : S} (p : Path M s s) (hp : 0 < p.length) (hs : p.sources.Nodup) :
    p.realize.val.IsSimpleCycle := by
  refine ⟨hp, p.realize.property.1.trans p.realize.property.2.symm, ?_⟩
  apply List.nodup_ofFn.mp
  rwa [realize_sources]

def castStart {a b c : S} (h : a = b) (p : Path M b c) : Path M a c := by
  cases h
  exact p

@[simp] theorem length_castStart {a b c : S} (h : a = b) (p : Path M b c) :
    (castStart h p).length = p.length := by cases h; rfl

@[simp] theorem cost_castStart {a b c : S} (h : a = b) (p : Path M b c) :
    (castStart h p).cost = p.cost := by cases h; rfl

def fromWalk : (l : ℕ) → (W : M.Walk l) → Path M (W.x 0) (W.x ⟨l, Nat.lt_succ_self l⟩)
  | 0, W => .nil (W.x 0)
  | l + 1, W => .cons (W.e 0) (castStart (W.valid 0) (fromWalk l (tail W)))

@[simp] theorem length_fromWalk (l : ℕ) (W : M.Walk l) : (fromWalk l W).length = l := by
  induction l with
  | zero => rfl
  | succ l ih =>
    change (castStart (W.valid 0) (fromWalk l (tail W))).length + 1 = l + 1
    exact (congrArg (fun z => z + 1) (length_castStart (W.valid 0) (fromWalk l (tail W)))).trans
      (congrArg (fun z => z + 1) (ih (tail W)))

@[simp] theorem cost_fromWalk (l : ℕ) (W : M.Walk l) : (fromWalk l W).cost = W.cost := by
  induction l with
  | zero => simp [fromWalk, cost, DetMDP.Walk.cost]
  | succ l ih =>
    change M.c (W.x 0) (W.e 0) + (castStart (W.valid 0) (fromWalk l (tail W))).cost = W.cost
    exact (congrArg (fun z => M.c (W.x 0) (W.e 0) + z)
      (cost_castStart (W.valid 0) (fromWalk l (tail W)))).trans
      ((congrArg (fun z => M.c (W.x 0) (W.e 0) + z) (ih (tail W))).trans
        (cost_tail W).symm)

end Path

end MDPProof


open MDPComplexity.StationaryHorizon
namespace MDPProof
variable {S : Type} [Fintype S] (M : DetMDP S)

instance finiteWalk (l : ℕ) : Finite (M.Walk l) := by
  let encode : M.Walk l → Σ x : Fin (l + 1) → S, (i : Fin l) → M.D (x i.castSucc) :=
    fun W => ⟨W.x, W.e⟩
  apply Finite.of_injective encode
  intro A B h
  cases A with
  | mk ax ae av =>
    cases B with
    | mk bx be bv =>
      have h' : (⟨ax, ae⟩ : Σ x : Fin (l + 1) → S, (i : Fin l) → M.D (x i.castSucc)) =
        ⟨bx, be⟩ := h
      cases h'
      rfl

noncomputable def walkOfPolicy (s : S) (δ : M.Policy) (T : ℕ) : M.Walk T where
  x := fun i => M.path s δ i.val
  e := fun i => δ (M.path s δ i.val) i.val
  valid := fun _ => rfl

@[simp] theorem walkOfPolicy_start (s : S) (δ : M.Policy) (T : ℕ) :
    (walkOfPolicy M s δ T).x 0 = s := rfl

@[simp] theorem walkOfPolicy_cost (s : S) (δ : M.Policy) (T : ℕ) :
    (walkOfPolicy M s δ T).cost = M.horizonCost s δ T := by
  unfold DetMDP.Walk.cost DetMDP.horizonCost DetMDP.stageCost walkOfPolicy
  exact Fin.sum_univ_eq_sum_range (fun i => M.c (M.path s δ i) (δ (M.path s δ i) i)) T

theorem minimum_walk {T : ℕ} (P : M.Walk T → Prop) (hP : ∃ W, P W) :
    ∃ W, P W ∧ ∀ V, P V → W.cost ≤ V.cost := by
  classical
  let : Fintype (M.Walk T) := Fintype.ofFinite _
  let A := Finset.univ.filter P
  have hA : A.Nonempty := by
    obtain ⟨W, hW⟩ := hP
    exact ⟨W, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hW⟩⟩
  obtain ⟨W, hW, hmin⟩ := Finset.exists_min_image A (fun W => W.cost) hA
  exact ⟨W, (Finset.mem_filter.mp hW).2, fun V hV =>
    hmin V (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hV⟩)⟩

noncomputable def policyOfWalk {T : ℕ} (W : M.Walk T) : M.Policy := by
  classical
  exact fun s t => if ht : t < T then
    if hs : W.x ⟨t, Nat.lt_succ_of_lt ht⟩ = s then hs ▸ W.e ⟨t, ht⟩
    else Classical.choice (M.nonemptyD s)
  else Classical.choice (M.nonemptyD s)

theorem policyOfWalk_on {T : ℕ} (W : M.Walk T) (i : Fin T) :
    policyOfWalk M W (W.x i.castSucc) i.val = W.e i := by
  classical
  unfold policyOfWalk
  split
  · split
    · rfl
    · rename_i h
      exact False.elim (h rfl)
  · rename_i h
    exact False.elim (h i.isLt)

theorem policyOfWalk_path {T : ℕ} (W : M.Walk T) (t : ℕ) (ht : t ≤ T) :
    M.path (W.x 0) (policyOfWalk M W) t = W.x ⟨t, Nat.lt_succ_of_le ht⟩ := by
  induction t with
  | zero => rfl
  | succ t ih =>
    have hlt : t < T := Nat.lt_of_succ_le ht
    have hp := ih (Nat.le_of_lt hlt)
    change M.next (M.path (W.x 0) (policyOfWalk M W) t)
      (policyOfWalk M W (M.path (W.x 0) (policyOfWalk M W) t) t) = _
    rw [hp]
    exact (congrArg (M.next _) (policyOfWalk_on M W ⟨t, hlt⟩)).trans (W.valid ⟨t, hlt⟩)

theorem policyOfWalk_cost {T : ℕ} (W : M.Walk T) :
    M.horizonCost (W.x 0) (policyOfWalk M W) T = W.cost := by
  unfold DetMDP.horizonCost DetMDP.Walk.cost
  rw [← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro i _
  unfold DetMDP.stageCost
  rw [policyOfWalk_path M W i.val (Nat.le_of_lt i.isLt)]
  exact congrArg (M.c _) (policyOfWalk_on M W i)

theorem optimum_walk (s : S) (T : ℕ) :
    ∃ W : M.Walk T, W.x 0 = s ∧ W.cost = M.optHorizon s T ∧
      ∀ V : M.Walk T, V.x 0 = s → W.cost ≤ V.cost := by
  classical
  let δ : M.Policy := fun q _ => Classical.choice (M.nonemptyD q)
  let : Nonempty M.Policy := ⟨δ⟩
  obtain ⟨W, hW, hmin⟩ := minimum_walk M (fun W : M.Walk T => W.x 0 = s)
    ⟨walkOfPolicy M s δ T, rfl⟩
  have hlo : ∀ π : M.Policy, W.cost ≤ M.horizonCost s π T := by
    intro π
    exact (hmin (walkOfPolicy M s π T) rfl).trans_eq (walkOfPolicy_cost M s π T)
  have hbounded : BddBelow (Set.range (fun π : M.Policy => M.horizonCost s π T)) := by
    refine ⟨W.cost, ?_⟩
    rintro z ⟨π, rfl⟩
    exact hlo π
  have hcost : M.horizonCost s (policyOfWalk M W) T = W.cost := by
    rw [← hW]
    exact policyOfWalk_cost M W
  refine ⟨W, hW, ?_, hmin⟩
  apply le_antisymm
  · exact le_ciInf hlo
  · exact (ciInf_le hbounded (policyOfWalk M W)).trans_eq hcost

end MDPProof


open MDPComplexity.StationaryHorizon
namespace MDPProof
variable {S : Type} [Fintype S] {M : DetMDP S}

structure Cycle (M : DetMDP S) where
  base : S
  path : Path M base base
  positive : 0 < path.length
  simple : path.sources.Nodup

namespace Cycle
variable (C : Cycle M)
def length : ℕ := C.path.length
def cost : ℝ := C.path.cost
def arcs : Multiset (Σ s, M.D s) := C.path.arcs
end Cycle

namespace Path

theorem decomposition {s t : S} (W : Path M s t) :
    ∃ P : Path M s t, P.vertices.Nodup ∧ ∃ Cs : List (Cycle M),
      P.length + (Cs.map Cycle.length).sum = W.length ∧
      P.cost + (Cs.map Cycle.cost).sum = W.cost ∧
      (P.arcs : Multiset (Σ s, M.D s)) + (Cs.map Cycle.arcs).sum = W.arcs := by
  classical
  induction W with
  | nil s =>
    exact ⟨.nil s, by simp [vertices], [], by simp [length], by simp [cost], by simp [arcs]⟩
  | @cons s t d W ih =>
    obtain ⟨P, hP, Cs, hlen, hcost, harcs⟩ := ih
    by_cases hs : s ∈ P.vertices
    · obtain ⟨A, B, rfl⟩ := split_vertex P hs
      have hnod : (A.sources ++ B.vertices).Nodup := by simpa only [vertices_append] using hP
      have hA : A.sources.Nodup := hnod.of_append_left
      have hB : B.vertices.Nodup := hnod.of_append_right
      have hnot : s ∉ A.sources := by
        intro h
        exact (List.disjoint_of_nodup_append hnod) h (source_mem B)
      let C : Cycle M := ⟨s, .cons d A, by simp [length], List.nodup_cons.mpr ⟨hnot, hA⟩⟩
      refine ⟨B, hB, C :: Cs, ?_, ?_, ?_⟩
      · simp only [List.map_cons, List.sum_cons, Cycle.length, C, length] at ⊢
        rw [length_append] at hlen
        omega
      · simp only [List.map_cons, List.sum_cons, Cycle.cost, C, cost] at ⊢
        rw [cost_append] at hcost
        linarith
      · simp only [List.map_cons, List.sum_cons, Cycle.arcs, C, arcs] at ⊢
        rw [arcs_append] at harcs
        simp only [← Multiset.coe_add, ← Multiset.cons_coe] at harcs ⊢
        simpa only [Multiset.cons_add, Multiset.add_cons, add_assoc, add_comm, add_left_comm] using
          congrArg (fun z => (⟨s, d⟩ : Σ s, M.D s) ::ₘ z) harcs
    · refine ⟨.cons d P, List.nodup_cons.mpr ⟨hs, hP⟩, Cs, ?_, ?_, ?_⟩
      · simp only [length]
        omega
      · simp only [cost]
        linarith
      · simp only [arcs, ← Multiset.cons_coe]
        simpa only [Multiset.cons_add] using
          congrArg (fun z => (⟨s, d⟩ : Σ s, M.D s) ::ₘ z) harcs

end Path
end MDPProof


open MDPComplexity.StationaryHorizon
namespace MDPProof
variable {S : Type} [Fintype S] {M : DetMDP S}

namespace Path

theorem first_crossing {s t : S} (p : Path M s t) (A : Set S)
    (hs : s ∈ A) (hm : ∃ v ∈ p.vertices, v ∉ A) :
    ∃ a ∈ p.arcs, a.1 ∈ A ∧ M.next a.1 a.2 ∉ A := by
  classical
  induction p with
  | nil s =>
    obtain ⟨v, hv, hn⟩ := hm
    have he : v = s := by simpa [vertices] using hv
    exact False.elim (hn (he ▸ hs))
  | @cons s t d p ih =>
    by_cases hn : M.next s d ∈ A
    · have hm' : ∃ v ∈ p.vertices, v ∉ A := by
        obtain ⟨v, hv, hnot⟩ := hm
        rcases List.mem_cons.mp hv with rfl | hv
        · exact False.elim (hnot hs)
        · exact ⟨v, hv, hnot⟩
      obtain ⟨a, ha, hsrc, htgt⟩ := ih hn hm'
      exact ⟨a, List.mem_cons_of_mem _ ha, hsrc, htgt⟩
    · exact ⟨⟨s, d⟩, List.mem_cons_self, hs, hn⟩

theorem simple_length_bound {s t : S} (p : Path M s t) (h : p.vertices.Nodup) :
    p.length + 1 ≤ Fintype.card S := by
  have hb := h.length_le_card
  simpa [vertices_eq, sources_length] using hb

end Path

namespace Cycle

theorem length_bound (C : Cycle M) : C.length ≤ Fintype.card S := by
  have h := C.simple.length_le_card
  simpa [length, Path.sources_length] using h

theorem mem_vertices_iff (C : Cycle M) (v : S) :
    v ∈ C.path.vertices ↔ v ∈ C.path.sources := by
  rw [Path.vertices_eq]
  simp only [List.mem_append, List.mem_singleton]
  constructor
  · rintro (h | rfl)
    · exact h
    · exact Path.start_mem_sources C.path C.positive
  · exact Or.inl

theorem rotate (C : Cycle M) (v : S) (hv : v ∈ C.path.vertices) :
    ∃ D : Cycle M, D.base = v ∧ D.length = C.length ∧ D.cost = C.cost ∧
      D.arcs = C.arcs ∧ ∀ w, w ∈ D.path.vertices ↔ w ∈ C.path.vertices := by
  obtain ⟨a, b, hab⟩ := Path.split_vertex C.path hv
  have hsimple : (b.append a).sources.Nodup := by
    rw [Path.sources_append]
    apply List.nodup_append_comm.mp
    simpa only [hab, Path.sources_append] using C.simple
  have hlen : (b.append a).length = C.path.length := by
    rw [hab, Path.length_append, Path.length_append, Nat.add_comm]
  let D : Cycle M := ⟨v, b.append a, hlen ▸ C.positive, hsimple⟩
  refine ⟨D, rfl, hlen, ?_, ?_, ?_⟩
  · change (b.append a).cost = C.path.cost
    rw [hab, Path.cost_append, Path.cost_append, add_comm]
  · change ((b.append a).arcs : Multiset (Σ s, M.D s)) = C.path.arcs
    rw [hab, Path.arcs_append, Path.arcs_append]
    simp only [← Multiset.coe_add, add_comm]
  · intro w
    rw [mem_vertices_iff D, mem_vertices_iff C]
    change w ∈ (b.append a).sources ↔ w ∈ C.path.sources
    rw [hab, Path.sources_append, Path.sources_append]
    simp only [List.mem_append, or_comm]

end Cycle

namespace Path

theorem splice {s t : S} (P : Path M s t) (C : Cycle M) (h : C.base ∈ P.vertices) :
    ∃ Q : Path M s t, Q.length = P.length + C.length ∧ Q.cost = P.cost + C.cost ∧
      (Q.arcs : Multiset (Σ s, M.D s)) = (P.arcs : Multiset (Σ s, M.D s)) + C.arcs ∧
      ∀ v, v ∈ Q.vertices ↔ v ∈ P.vertices ∨ v ∈ C.path.vertices := by
  obtain ⟨a, b, rfl⟩ := split_vertex P h
  refine ⟨a.append (C.path.append b), ?_, ?_, ?_, ?_⟩
  · simp only [length_append, Cycle.length]
    omega
  · simp only [cost_append, Cycle.cost]
    ring
  · simp only [arcs_append, ← Multiset.coe_add, Cycle.arcs]
    ac_rfl
  · intro v
    simp only [mem_vertices_append]
    tauto

theorem mem_cycle_sum (Cs : List (Cycle M)) (a : Σ s, M.D s) :
    a ∈ (Cs.map Cycle.arcs).sum ↔ ∃ C ∈ Cs, a ∈ C.arcs := by
  induction Cs with
  | nil => simp
  | cons C Cs ih => simp [ih, or_and_right, exists_or, eq_comm]

theorem crossing_cycle {s t : S} (W B : Path M s t) (Cs : List (Cycle M))
    (ha : (B.arcs : Multiset (Σ s, M.D s)) + (Cs.map Cycle.arcs).sum = W.arcs)
    (hm : ∃ v ∈ W.vertices, v ∉ B.vertices) :
    ∃ C ∈ Cs, ∃ v ∈ C.path.vertices, v ∈ B.vertices ∧
      ∃ w ∈ C.path.vertices, w ∉ B.vertices := by
  obtain ⟨a, haw, hin, hout⟩ := first_crossing W {v | v ∈ B.vertices} (source_mem B) hm
  have ham : a ∈ (W.arcs : Multiset (Σ s, M.D s)) := haw
  rw [← ha, Multiset.mem_add] at ham
  rcases ham with hb | hc
  · exact False.elim (hout ((arc_endpoints B a hb).2))
  · obtain ⟨C, hC, hac⟩ := (mem_cycle_sum Cs a).mp hc
    have he := arc_endpoints C.path a hac
    exact ⟨C, hC, a.1, he.1, hin, M.next a.1 a.2, he.2, hout⟩

theorem grow {s t : S} (W B : Path M s t) (Cs : List (Cycle M))
    (ha : (B.arcs : Multiset (Σ s, M.D s)) + (Cs.map Cycle.arcs).sum = W.arcs)
    (hm : ∃ v ∈ W.vertices, v ∉ B.vertices) :
    ∃ Q : Path M s t, ∃ Ds : List (Cycle M),
      Q.length ≤ B.length + Fintype.card S ∧
      Q.length + (Ds.map Cycle.length).sum = B.length + (Cs.map Cycle.length).sum ∧
      Q.cost + (Ds.map Cycle.cost).sum = B.cost + (Cs.map Cycle.cost).sum ∧
      (Q.arcs : Multiset (Σ s, M.D s)) + (Ds.map Cycle.arcs).sum = W.arcs ∧
      (∀ C ∈ Ds, C ∈ Cs) ∧
      (∀ v ∈ B.vertices, v ∈ Q.vertices) ∧ ∃ v ∈ Q.vertices, v ∉ B.vertices := by
  classical
  obtain ⟨C, hC, v, hvC, hvB, w, hwC, hwB⟩ := crossing_cycle W B Cs ha hm
  obtain ⟨D, hbase, hlen, hcost, harcs, hverts⟩ := C.rotate v hvC
  have hDb : D.base ∈ B.vertices := hbase ▸ hvB
  obtain ⟨Q, hQl, hQc, hQa, hQv⟩ := splice B D hDb
  obtain ⟨L, R, hLR⟩ := List.append_of_mem hC
  subst Cs
  refine ⟨Q, L ++ R, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hQl, hlen]
    exact Nat.add_le_add_left C.length_bound _
  · simp only [List.map_append, List.map_cons, List.sum_append, List.sum_cons]
    rw [hQl, hlen]
    omega
  · simp only [List.map_append, List.map_cons, List.sum_append, List.sum_cons]
    rw [hQc, hcost]
    ring
  · rw [hQa, harcs]
    simp only [List.map_append, List.map_cons, List.sum_append, List.sum_cons] at ha ⊢
    convert ha using 1
    ac_rfl
  · intro E hE
    simp only [List.mem_append, List.mem_cons] at hE ⊢
    tauto
  · intro z hz
    exact (hQv z).mpr (Or.inl hz)
  · exact ⟨w, (hQv w).mpr (Or.inr ((hverts w).mpr hwC)), hwB⟩

theorem cover_all [DecidableEq S] {s t : S} (W B : Path M s t) (Cs : List (Cycle M))
    (ha : (B.arcs : Multiset (Σ s, M.D s)) + (Cs.map Cycle.arcs).sum = W.arcs) :
    ∃ Q : Path M s t, ∃ Ds : List (Cycle M),
      Q.length ≤ B.length + Fintype.card S * (Fintype.card S - B.vertices.toFinset.card) ∧
      Q.length + (Ds.map Cycle.length).sum = B.length + (Cs.map Cycle.length).sum ∧
      Q.cost + (Ds.map Cycle.cost).sum = B.cost + (Cs.map Cycle.cost).sum ∧
      (Q.arcs : Multiset (Σ s, M.D s)) + (Ds.map Cycle.arcs).sum = W.arcs ∧
      (∀ C ∈ Ds, C ∈ Cs) ∧
      (∀ v ∈ B.vertices, v ∈ Q.vertices) ∧ ∀ v ∈ W.vertices, v ∈ Q.vertices := by
  classical
  generalize he : Fintype.card S - B.vertices.toFinset.card = m
  induction m using Nat.strong_induction_on generalizing B Cs with
  | h m ih =>
    by_cases hc : ∀ v ∈ W.vertices, v ∈ B.vertices
    · exact ⟨B, Cs, Nat.le_add_right _ _, rfl, rfl, ha, fun _ h => h, fun _ h => h, hc⟩
    · have hm : ∃ v ∈ W.vertices, v ∉ B.vertices := by push Not at hc; exact hc
      obtain ⟨Q, Ds, hQl, hlen, hcost, harcs, hDs, hsub, hnew⟩ := grow W B Cs ha hm
      have hfin : B.vertices.toFinset ⊆ Q.vertices.toFinset := by
        intro v hv
        exact List.mem_toFinset.mpr (hsub v (List.mem_toFinset.mp hv))
      have hne : B.vertices.toFinset ≠ Q.vertices.toFinset := by
        intro heq
        obtain ⟨v, hv, hn⟩ := hnew
        have hmem := List.mem_toFinset.mpr hv
        rw [← heq] at hmem
        exact hn (List.mem_toFinset.mp hmem)
      have hcard := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hfin, hne⟩)
      have hQcard := Finset.card_le_univ Q.vertices.toFinset
      have hdiff : Fintype.card S - Q.vertices.toFinset.card < m := by omega
      obtain ⟨R, Es, hRl, hRlens, hRcost, hRarcs, hEs, hQR, hWR⟩ :=
        ih (Fintype.card S - Q.vertices.toFinset.card) hdiff Q Ds harcs rfl
      refine ⟨R, Es, ?_, hRlens.trans hlen, hRcost.trans hcost, hRarcs,
        fun C hC => hDs C (hEs C hC), fun v hv => hQR v (hsub v hv), hWR⟩
      have hdiff' : Fintype.card S - Q.vertices.toFinset.card + 1 ≤ m := by omega
      have hmul := Nat.mul_le_mul_left (Fintype.card S) hdiff'
      nlinarith

theorem sources_eq_map {s t : S} (P : Path M s t) : P.sources = P.arcs.map Sigma.fst := by
  induction P with
  | nil => rfl
  | cons d P ih => simp [sources, arcs, ih]

theorem cycle_support {s t : S} (W P : Path M s t) (Cs : List (Cycle M))
    (ha : (P.arcs : Multiset (Σ s, M.D s)) + (Cs.map Cycle.arcs).sum = W.arcs)
    (C : Cycle M) (hC : C ∈ Cs) (v : S) (hv : v ∈ C.path.vertices) : v ∈ W.vertices := by
  have hsv := (C.mem_vertices_iff v).mp hv
  rw [sources_eq_map, List.mem_map] at hsv
  obtain ⟨a, haC, rfl⟩ := hsv
  have ham : a ∈ (Cs.map Cycle.arcs).sum := (mem_cycle_sum Cs a).mpr ⟨C, hC, haC⟩
  have haw : a ∈ (W.arcs : Multiset (Σ s, M.D s)) := by
    rw [← ha, Multiset.mem_add]
    exact Or.inr ham
  exact (arc_endpoints W a haw).1

theorem skeleton {s t : S} (W : Path M s t) (hW : Fintype.card S ≤ W.length) :
    ∃ Cs : List (Cycle M), Cs ≠ [] ∧ ∃ Q : Path M s t, ∃ Ds : List (Cycle M),
      Q.length + 1 ≤ Fintype.card S * Fintype.card S ∧
      Q.length + (Ds.map Cycle.length).sum = W.length ∧
      Q.cost + (Ds.map Cycle.cost).sum = W.cost ∧
      (Q.arcs : Multiset (Σ s, M.D s)) + (Ds.map Cycle.arcs).sum = W.arcs ∧
      (∀ C ∈ Ds, C ∈ Cs) ∧ ∀ C ∈ Cs, ∀ v ∈ C.path.vertices, v ∈ Q.vertices := by
  classical
  obtain ⟨P, hP, Cs, hl, hc, ha⟩ := W.decomposition
  have hpbound := P.simple_length_bound hP
  have hne : Cs ≠ [] := by
    intro he
    subst Cs
    simp only [List.map_nil, List.sum_nil, Nat.add_zero] at hl
    omega
  obtain ⟨Q, Ds, hQl, hDl, hDc, hDa, hsub, _, hcover⟩ := cover_all W P Cs ha
  refine ⟨Cs, hne, Q, Ds, ?_, hDl.trans hl, hDc.trans hc, hDa, hsub, ?_⟩
  · have hcard : P.vertices.toFinset.card = P.length + 1 := by
      rw [List.toFinset_card_of_nodup hP, vertices_eq]
      simp
    rw [hcard] at hQl
    have hsubn := Nat.sub_add_cancel hpbound
    have hn : 0 < Fintype.card S := Fintype.card_pos_iff.mpr ⟨s⟩
    nlinarith
  · intro C hC v hv
    exact hcover v (cycle_support W P Cs ha C hC v hv)

end Path
end MDPProof


open MDPComplexity.StationaryHorizon
namespace MDPProof
variable {S : Type} [Fintype S] {M : DetMDP S}

namespace Cycle

theorem minimum_mean (Cs : List (Cycle M)) (hne : Cs ≠ []) :
    ∃ C ∈ Cs, ∀ D ∈ Cs, (D.length : ℝ) * C.cost ≤ (C.length : ℝ) * D.cost := by
  classical
  have hn : Cs.toFinset.Nonempty := by
    cases Cs with
    | nil => exact False.elim (hne rfl)
    | cons C Cs => exact ⟨C, by simp⟩
  obtain ⟨C, hC, hm⟩ := Finset.exists_min_image Cs.toFinset
    (fun D => D.cost / (D.length : ℝ)) hn
  refine ⟨C, List.mem_toFinset.mp hC, ?_⟩
  intro D hD
  have h := hm D (List.mem_toFinset.mpr hD)
  have hCp : (0 : ℝ) < C.length := by exact_mod_cast C.positive
  have hDp : (0 : ℝ) < D.length := by exact_mod_cast D.positive
  have hmul := (div_le_div_iff₀ hCp hDp).mp h
  nlinarith

def countLength (Cs : List (Cycle M)) (j : ℕ) : ℕ :=
  (Cs.filter (fun C => C.length == j)).length

@[simp] theorem countLength_nil (j : ℕ) : countLength ([] : List (Cycle M)) j = 0 := rfl

@[simp] theorem countLength_cons (C : Cycle M) (Cs : List (Cycle M)) (j : ℕ) :
    countLength (C :: Cs) j = (if C.length = j then 1 else 0) + countLength Cs j := by
  by_cases h : C.length = j
  · simp [countLength, h, Nat.add_comm]
  · simp [countLength, h]

theorem mean_sum (C : Cycle M) (Ds : List (Cycle M))
    (h : ∀ D ∈ Ds, (D.length : ℝ) * C.cost ≤ (C.length : ℝ) * D.cost) :
    ((Ds.map length).sum : ℝ) * C.cost ≤ (C.length : ℝ) * (Ds.map cost).sum := by
  induction Ds with
  | nil => simp
  | cons D Ds ih =>
    have hD := h D List.mem_cons_self
    have hDs := ih (fun E hE => h E (List.mem_cons_of_mem D hE))
    simp only [List.map_cons, List.sum_cons, Nat.cast_add]
    nlinarith

theorem filter_partition_sum {α : Type*} [AddCommMonoid α] (f : Cycle M → α)
    (Ds : List (Cycle M)) (j : ℕ) :
    ((Ds.filter (fun D => D.length == j)).map f).sum +
      ((Ds.filter (fun D => D.length != j)).map f).sum = (Ds.map f).sum := by
  induction Ds with
  | nil => simp
  | cons D Ds ih =>
    by_cases h : D.length = j
    · simpa [h, add_assoc] using congrArg (fun z => f D + z) ih
    · simpa [h, add_assoc, add_left_comm] using congrArg (fun z => f D + z) ih

theorem countLength_filter_ne (Ds : List (Cycle M)) (j i : ℕ) :
    countLength (Ds.filter (fun D => D.length != j)) i =
      if i = j then 0 else countLength Ds i := by
  induction Ds with
  | nil => simp
  | cons D Ds ih =>
    by_cases hi : D.length = i <;> by_cases hj : D.length = j <;>
      simp_all [countLength]

theorem sum_length_filter (Ds : List (Cycle M)) (j : ℕ) :
    ((Ds.filter (fun D => D.length == j)).map length).sum = j * countLength Ds j := by
  induction Ds with
  | nil => simp
  | cons D Ds ih =>
    by_cases h : D.length = j
    · simp only [List.filter_cons, h, beq_self_eq_true, ite_true, List.map_cons, List.sum_cons,
        countLength_cons]
      rw [ih]
      ring
    · simp [h, ih]

theorem filter_group_cost (C : Cycle M) (Ds : List (Cycle M)) (j : ℕ)
    (hmean : ∀ D ∈ Ds, (D.length : ℝ) * C.cost ≤ (C.length : ℝ) * D.cost)
    (hcount : countLength Ds j = C.length) :
    (j : ℝ) * C.cost ≤ ((Ds.filter (fun D => D.length == j)).map cost).sum := by
  have hs := mean_sum C (Ds.filter (fun D => D.length == j))
    (fun D hD => hmean D (List.mem_filter.mp hD).1)
  rw [sum_length_filter, hcount, Nat.cast_mul] at hs
  have hp : (0 : ℝ) < C.length := by exact_mod_cast C.positive
  nlinarith

theorem reduce (C : Cycle M) (Ds : List (Cycle M))
    (hmean : ∀ D ∈ Ds, (D.length : ℝ) * C.cost ≤ (C.length : ℝ) * D.cost) :
    ∃ Rs : List (Cycle M), ∃ m : ℕ,
      (∀ D ∈ Rs, D ∈ Ds) ∧
      (Rs.map length).sum + m * C.length = (Ds.map length).sum ∧
      (Rs.map cost).sum + (m : ℝ) * C.cost ≤ (Ds.map cost).sum ∧
      countLength Rs C.length = 0 ∧ ∀ j, countLength Rs j < C.length := by
  induction Ds with
  | nil =>
    refine ⟨[], 0, by simp, by simp, by simp, rfl, ?_⟩
    intro j
    exact C.positive
  | cons E Ds ih =>
    obtain ⟨Rs, m, hsub, hlen, hcost, hzero, hcount⟩ :=
      ih (fun D hD => hmean D (List.mem_cons_of_mem E hD))
    have hE := hmean E List.mem_cons_self
    have hp : (0 : ℝ) < C.length := by exact_mod_cast C.positive
    by_cases he : E.length = C.length
    · refine ⟨Rs, m + 1, fun D hD => List.mem_cons_of_mem E (hsub D hD), ?_, ?_, hzero, hcount⟩
      · simp only [List.map_cons, List.sum_cons, he]
        nlinarith
      · have hEc : C.cost ≤ E.cost := by rw [he] at hE; nlinarith
        simp only [List.map_cons, List.sum_cons, Nat.cast_add, Nat.cast_one]
        nlinarith
    · have hmean' : ∀ D ∈ E :: Rs, (D.length : ℝ) * C.cost ≤ (C.length : ℝ) * D.cost := by
        intro D hD
        rcases List.mem_cons.mp hD with rfl | hD
        · exact hE
        · exact hmean D (List.mem_cons_of_mem E (hsub D hD))
      have hsub' : ∀ D ∈ E :: Rs, D ∈ E :: Ds := by
        intro D hD
        rcases List.mem_cons.mp hD with rfl | hD
        · exact List.mem_cons_self
        · exact List.mem_cons_of_mem E (hsub D hD)
      by_cases hc : countLength (E :: Rs) E.length < C.length
      · refine ⟨E :: Rs, m, hsub', ?_, ?_, ?_, ?_⟩
        · simp only [List.map_cons, List.sum_cons]
          omega
        · simp only [List.map_cons, List.sum_cons]
          linarith
        · simp only [countLength_cons, if_neg he, zero_add, hzero]
        · intro j
          by_cases hj : j = E.length
          · exact hj ▸ hc
          · have hej : E.length ≠ j := Ne.symm hj
            simpa only [countLength_cons, if_neg hej, zero_add] using hcount j
      · have heq : countLength (E :: Rs) E.length = C.length := by
          have hr := hcount E.length
          have hce : countLength (E :: Rs) E.length = 1 + countLength Rs E.length := by simp
          omega
        let R := (E :: Rs).filter (fun D => D.length != E.length)
        have hpartL := filter_partition_sum length (E :: Rs) E.length
        have hpartC := filter_partition_sum cost (E :: Rs) E.length
        have hgroup := filter_group_cost C (E :: Rs) E.length hmean' heq
        rw [sum_length_filter, heq] at hpartL
        refine ⟨R, m + E.length, ?_, ?_, ?_, ?_, ?_⟩
        · intro D hD
          exact hsub' D (List.mem_filter.mp hD).1
        · simp only [List.map_cons, List.sum_cons] at hpartL ⊢
          change E.length * C.length + (R.map length).sum = E.length + (Rs.map length).sum at hpartL
          nlinarith
        · simp only [List.map_cons, List.sum_cons] at hpartC ⊢
          change _ + (R.map cost).sum = E.cost + (Rs.map cost).sum at hpartC
          push_cast
          nlinarith
        · rw [countLength_filter_ne, if_neg (Ne.symm he)]
          simp only [countLength_cons, if_neg he, zero_add, hzero]
        · intro j
          rw [countLength_filter_ne]
          by_cases hj : j = E.length
          · rw [if_pos hj]
            exact C.positive
          · rw [if_neg hj]
            simpa only [countLength_cons, if_neg (Ne.symm hj), zero_add] using hcount j

theorem length_sum_counts (Ds : List (Cycle M)) :
    (Ds.map length).sum = ∑ j ∈ Finset.range (Fintype.card S + 1), j * countLength Ds j := by
  induction Ds with
  | nil => simp
  | cons D Ds ih =>
    simp only [List.map_cons, List.sum_cons, ih]
    simp_rw [countLength_cons, Nat.mul_add]
    rw [Finset.sum_add_distrib]
    congr 1
    have hD : D.length ∈ Finset.range (Fintype.card S + 1) :=
      Finset.mem_range.mpr (Nat.lt_succ_of_le D.length_bound)
    simp [hD, eq_comm]

theorem residual_bound (C : Cycle M) (Rs : List (Cycle M))
    (hc : ∀ j, countLength Rs j < C.length) :
    2 * (Rs.map length).sum ≤ (Fintype.card S - 1) * Fintype.card S * (Fintype.card S + 1) := by
  have hcount : ∀ j, countLength Rs j ≤ Fintype.card S - 1 := by
    intro j
    have hj := hc j
    have hk := C.length_bound
    omega
  have hs : (Rs.map length).sum ≤
      (Fintype.card S - 1) * ∑ j ∈ Finset.range (Fintype.card S + 1), j := by
    rw [length_sum_counts, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j _
    have h := Nat.mul_le_mul_left j (hcount j)
    simpa only [Nat.mul_comm] using h
  have ht := Finset.sum_range_id_mul_two (Fintype.card S + 1)
  simp only [Nat.add_sub_cancel] at ht
  nlinarith

end Cycle
namespace Path

theorem splice_many {s t : S} (B : Path M s t) (Cs : List (Cycle M))
    (h : ∀ C ∈ Cs, C.base ∈ B.vertices) :
    ∃ P : Path M s t, P.length = B.length + (Cs.map Cycle.length).sum ∧
      P.cost = B.cost + (Cs.map Cycle.cost).sum ∧
      ∀ v ∈ B.vertices, v ∈ P.vertices := by
  induction Cs with
  | nil => exact ⟨B, by simp, by simp, fun _ hv => hv⟩
  | cons C Cs ih =>
    obtain ⟨P, hPl, hPc, hPv⟩ := ih (fun D hD => h D (List.mem_cons_of_mem C hD))
    obtain ⟨Q, hQl, hQc, _, hQv⟩ := splice P C (hPv C.base (h C List.mem_cons_self))
    refine ⟨Q, ?_, ?_, fun v hv => (hQv v).mpr (Or.inl (hPv v hv))⟩
    · simp only [List.map_cons, List.sum_cons]
      omega
    · simp only [List.map_cons, List.sum_cons]
      linarith

end Path

theorem cubic_bound {n b r : ℕ} (hn : 1 ≤ n) (hb : b + 1 ≤ n * n)
    (hr : 2 * r ≤ (n - 1) * n * (n + 1)) : b + r < n ^ 3 := by
  have hs : n - 1 + 1 = n := Nat.sub_add_cancel hn
  have hpos : 0 ≤ n * (n - 1) ^ 2 := Nat.zero_le _
  nlinarith

namespace Path

theorem short_cycle_cost {s t : S} (W : Path M s t) (hW : Fintype.card S ≤ W.length) :
    ∃ P : Path M s t, ∃ C : Cycle M, ∃ m : ℕ,
      P.length + m * C.length = W.length ∧
      P.length < (Fintype.card S) ^ 3 ∧
      C.base ∈ P.vertices ∧ P.cost + (m : ℝ) * C.cost ≤ W.cost := by
  classical
  obtain ⟨Cs, hne, B, Ds, hBbound, hDl, hDc, _, hsub, hcover⟩ := W.skeleton hW
  obtain ⟨C, hC, hmean⟩ := Cycle.minimum_mean Cs hne
  obtain ⟨Rs, m, hRs, hRl, hRc, _, hcount⟩ :=
    Cycle.reduce C Ds (fun D hD => hmean D (hsub D hD))
  obtain ⟨P, hPl, hPc, hPv⟩ := splice_many B Rs
    (fun D hD => hcover D (hsub D (hRs D hD)) D.base (source_mem D.path))
  refine ⟨P, C, m, ?_, ?_, ?_, ?_⟩
  · omega
  · rw [hPl]
    exact cubic_bound (Fintype.card_pos_iff.mpr ⟨s⟩) hBbound (Cycle.residual_bound C Rs hcount)
  · exact hPv C.base (hcover C hC C.base (source_mem C.path))
  · linarith

end Path

end MDPProof


open MDPComplexity.StationaryHorizon
namespace MDPProof
variable {S : Type} [Fintype S] {M : DetMDP S}

namespace Path

@[simp] theorem vertices_castStart {a b c : S} (h : a = b) (p : Path M b c) :
    (castStart h p).vertices = p.vertices := by cases h; rfl

@[simp] theorem vertices_fromWalk (l : ℕ) (W : M.Walk l) :
    (fromWalk l W).vertices = List.ofFn W.x := by
  induction l with
  | zero =>
    change [W.x 0] = List.ofFn W.x
    rw [List.ofFn_succ]
    rfl
  | succ l ih =>
    rw [List.ofFn_succ]
    change W.x 0 :: (castStart (W.valid 0) (fromWalk l (tail W))).vertices =
      W.x 0 :: List.ofFn (tail W).x
    exact congrArg (List.cons (W.x 0))
      ((vertices_castStart (W.valid 0) (fromWalk l (tail W))).trans (ih (tail W)))

def castEnd {a b c : S} (h : b = c) (p : Path M a b) : Path M a c := by cases h; exact p
@[simp] theorem length_castEnd {a b c : S} (h : b = c) (p : Path M a b) :
    (castEnd h p).length = p.length := by cases h; rfl
@[simp] theorem cost_castEnd {a b c : S} (h : b = c) (p : Path M a b) :
    (castEnd h p).cost = p.cost := by cases h; rfl

def loops {u : S} (p : Path M u u) : ℕ → Path M u u
  | 0 => .nil u
  | m + 1 => p.append (p.loops m)

@[simp] theorem length_loops {u : S} (p : Path M u u) (m : ℕ) :
    (p.loops m).length = m * p.length := by
  induction m with
  | zero => simp [loops, length]
  | succ m ih => simp [loops, length_append, ih, Nat.add_mul, Nat.add_comm]

@[simp] theorem cost_loops {u : S} (p : Path M u u) (m : ℕ) :
    (p.loops m).cost = (m : ℝ) * p.cost := by
  induction m with
  | zero => simp [loops, cost]
  | succ m ih => simp [loops, cost_append, ih, add_mul, add_comm]

theorem splice_loop {s t u : S} (P : Path M s t) (L : Path M u u) (h : u ∈ P.vertices) :
    ∃ Q : Path M s t, Q.length = P.length + L.length ∧ Q.cost = P.cost + L.cost := by
  obtain ⟨a, b, rfl⟩ := split_vertex P h
  refine ⟨a.append (L.append b), ?_, ?_⟩
  · simp only [length_append]
    omega
  · simp only [cost_append]
    ring

end Path

def castWalk {l r : ℕ} (h : l = r) (W : M.Walk l) : M.Walk r := h ▸ W
@[simp] theorem castWalk_cost {l r : ℕ} (h : l = r) (W : M.Walk l) :
    (castWalk h W).cost = W.cost := by cases h; rfl
@[simp] theorem castWalk_start {l r : ℕ} (h : l = r) (W : M.Walk l) :
    (castWalk h W).x 0 = W.x 0 := by cases h; rfl

theorem loops_splice {l k : ℕ} (W : M.Walk l) (C : M.Walk k) (u : S)
    (hvisit : ∃ t : Fin (l + 1), W.x t = u)
    (hstart : C.x 0 = u) (hend : C.x ⟨k, Nat.lt_succ_self k⟩ = u) (m : ℕ) :
    ∃ V : M.Walk (l + m * k), V.x 0 = W.x 0 ∧ V.cost = W.cost + (m : ℝ) * C.cost := by
  let p := Path.fromWalk l W
  let q := Path.castStart hstart.symm (Path.castEnd hend (Path.fromWalk k C))
  have hpl : p.length = l := Path.length_fromWalk l W
  have hpc : p.cost = W.cost := Path.cost_fromWalk l W
  have hql : q.length = k := by simp [q]
  have hqc : q.cost = C.cost := by simp [q]
  have hv : u ∈ p.vertices := by
    rw [Path.vertices_fromWalk]
    obtain ⟨i, hi⟩ := hvisit
    exact List.mem_ofFn.mpr ⟨i, hi⟩
  obtain ⟨r, hrl, hrc⟩ := Path.splice_loop p (q.loops m) hv
  have hr : r.length = l + m * k := by rw [hrl, Path.length_loops, hpl, hql]
  refine ⟨castWalk hr r.realize.val, ?_, ?_⟩
  · exact (castWalk_start hr r.realize.val).trans r.realize.property.1
  · rw [castWalk_cost, Path.realize_cost, hrc, Path.cost_loops, hpc, hqc]

end MDPProof

namespace MDPComplexity.StationaryHorizon

variable {S : Type} [Fintype S]

/-- §3, p. 447: corrected numerical form of the short-prefix/one-cycle structure.
The prefix visits the cycle base, so copies of that cycle can be inserted there. -/
theorem short_prefix_cycle (M : DetMDP S) (s₀ : S) (T : ℕ)
    (hT : (Fintype.card S) ^ 2 < T) :
    ∃ (W : M.Walk T) (l k : ℕ) (u : S) (P : M.Walk l) (C : M.Walk k),
      W.x 0 = s₀ ∧
      IsLeast {y : ℝ | ∃ V : M.Walk T, V.x 0 = s₀ ∧ y = V.cost} W.cost ∧
      l ≤ T ∧ l < (Fintype.card S) ^ 3 ∧
      1 ≤ k ∧ k ≤ Fintype.card S ∧ k ∣ T - l ∧
      P.x 0 = s₀ ∧ (∃ t : Fin (l + 1), P.x t = u) ∧
      C.IsSimpleCycle ∧ C.x 0 = u ∧
      W.cost = P.cost + (((T - l) / k : ℕ) : ℝ) * C.cost := by
  obtain ⟨W, hWs, _, hmin⟩ := MDPProof.optimum_walk M s₀ T
  have hn : 0 < Fintype.card S := Fintype.card_pos_iff.mpr ⟨s₀⟩
  have hNT : Fintype.card S ≤ T := by nlinarith
  have hpath : Fintype.card S ≤ (MDPProof.Path.fromWalk T W).length := by
    simpa only [MDPProof.Path.length_fromWalk] using hNT
  obtain ⟨P, C, m, hlen, hbound, hbase, hcost⟩ :=
    MDPProof.Path.short_cycle_cost (MDPProof.Path.fromWalk T W) hpath
  rw [MDPProof.Path.length_fromWalk] at hlen
  rw [MDPProof.Path.cost_fromWalk] at hcost
  have hvisit : ∃ i, P.realize.val.x i = C.base := by
    apply List.mem_ofFn.mp
    rwa [MDPProof.Path.realize_vertices]
  have hsimple := MDPProof.Path.realize_cycle C.path C.positive C.simple
  have hCstart := C.path.realize.property.1
  have hCend := C.path.realize.property.2
  obtain ⟨V, hVs, hVc⟩ := MDPProof.loops_splice P.realize.val C.path.realize.val C.base
    hvisit hCstart hCend m
  have hVstart : (MDPProof.castWalk hlen V).x 0 = s₀ :=
    (MDPProof.castWalk_start hlen V).trans (hVs.trans (P.realize.property.1.trans hWs))
  have hminV := hmin (MDPProof.castWalk hlen V) hVstart
  have hminV' : W.cost ≤ P.realize.val.cost + (m : ℝ) * C.path.realize.val.cost :=
    hminV.trans_eq ((MDPProof.castWalk_cost hlen V).trans hVc)
  have hcost' : P.realize.val.cost + (m : ℝ) * C.path.realize.val.cost ≤ W.cost := by
    simpa only [MDPProof.Path.realize_cost, MDPProof.Cycle.cost] using hcost
  have heq : W.cost = P.realize.val.cost + (m : ℝ) * C.path.realize.val.cost :=
    le_antisymm hminV' hcost'
  have hsub : T - P.length = m * C.length := by omega
  have hdiv : (T - P.length) / C.length = m := by
    rw [hsub]
    exact Nat.mul_div_cancel m C.positive
  refine ⟨W, P.length, C.length, C.base, P.realize.val, C.path.realize.val,
    hWs, ⟨⟨W, hWs, rfl⟩, ?_⟩, ?_, hbound, C.positive, C.length_bound, ?_,
    P.realize.property.1.trans hWs, hvisit, hsimple, hCstart, ?_⟩
  · rintro y ⟨U, hUs, rfl⟩
    exact hmin U hUs
  · omega
  · exact ⟨m, by simpa only [Nat.mul_comm] using hsub⟩
  · rw [hdiv]
    exact heq


end MDPComplexity.StationaryHorizon


open MDPComplexity.StationaryHorizon
namespace MDPProof
variable {S : Type} [Fintype S] (M : DetMDP S)

theorem optimum_isLeast (s : S) (T : ℕ) :
    IsLeast {y : ℝ | ∃ W : M.Walk T, W.x 0 = s ∧ y = W.cost} (M.optHorizon s T) := by
  obtain ⟨W, hWs, hWc, hmin⟩ := optimum_walk M s T
  refine ⟨⟨W, hWs, hWc.symm⟩, ?_⟩
  rintro y ⟨V, hVs, rfl⟩
  exact hWc ▸ hmin V hVs

theorem candidate_lower (s : S) (T l k : ℕ) (u : S) (w r : ℝ)
    (hl : l ≤ T) (hd : k ∣ T - l)
    (hw : IsLeast {y : ℝ | ∃ W : M.Walk l,
      W.x 0 = s ∧ (∃ t : Fin (l + 1), W.x t = u) ∧ y = W.cost} w)
    (hr : IsLeast {y : ℝ | ∃ C : M.Walk k,
      C.x 0 = u ∧ C.x ⟨k, Nat.lt_succ_self k⟩ = u ∧ y = C.cost} r) :
    M.optHorizon s T ≤ w + (((T - l) / k : ℕ) : ℝ) * r := by
  obtain ⟨W, hWs, hvisit, hWc⟩ := hw.1
  obtain ⟨C, hCs, hCe, hCc⟩ := hr.1
  obtain ⟨V, hVs, hVc⟩ := loops_splice W C u hvisit hCs hCe ((T-l)/k)
  have hlen : l + ((T-l)/k) * k = T := by
    rw [Nat.div_mul_cancel hd, Nat.add_sub_of_le hl]
  have hstart : (castWalk hlen V).x 0 = s :=
    (castWalk_start hlen V).trans (hVs.trans hWs)
  have hcost : (castWalk hlen V).cost = w + (((T-l)/k : ℕ) : ℝ) * r := by
    rw [castWalk_cost, hVc, ← hWc, ← hCc]
  exact ((optimum_isLeast M s T).2 ⟨castWalk hlen V, hstart, rfl⟩).trans_eq hcost

end MDPProof

namespace MDPComplexity.StationaryHorizon

variable {S : Type} [Fintype S]

/-- §3, p. 447, identity underlying Theorem 5: minimize over a short prefix through
`u` and a repeated closed `k`-walk at `u`. The minima in each component are genuine
walk minima, and the outer optimum remains over all time-dependent policies. -/
theorem theorem5_structure (M : DetMDP S) (s₀ : S) (T : ℕ)
    (hT : (Fintype.card S) ^ 2 < T) :
    IsLeast
      {x : ℝ | ∃ (l k : ℕ) (u : S) (w r : ℝ),
        l ≤ T ∧ l < (Fintype.card S) ^ 3 ∧
        1 ≤ k ∧ k ≤ Fintype.card S ∧ k ∣ T - l ∧
        IsLeast {y : ℝ | ∃ W : M.Walk l,
          W.x 0 = s₀ ∧ (∃ t : Fin (l + 1), W.x t = u) ∧ y = W.cost} w ∧
        IsLeast {y : ℝ | ∃ C : M.Walk k,
          C.x 0 = u ∧ C.x ⟨k, Nat.lt_succ_self k⟩ = u ∧ y = C.cost} r ∧
        x = w + (((T - l) / k : ℕ) : ℝ) * r}
      (M.optHorizon s₀ T) := by
  have hleast := MDPProof.optimum_isLeast M s₀ T
  refine ⟨?_, ?_⟩
  · obtain ⟨W, l, k, u, P, C, hWs, hWmin, hl, hbound, hkpos, hkbound, hd,
      hPs, hvisit, hsimple, hCs, hcost⟩ := short_prefix_cycle M s₀ T hT
    have hCe : C.x ⟨k, Nat.lt_succ_self k⟩ = u := hsimple.2.1.symm.trans hCs
    obtain ⟨Pmin, hPm, hPmin⟩ := MDPProof.minimum_walk M
      (fun V : M.Walk l => V.x 0 = s₀ ∧ ∃ t : Fin (l+1), V.x t = u) ⟨P, hPs, hvisit⟩
    obtain ⟨Cmin, hCm, hCmin⟩ := MDPProof.minimum_walk M
      (fun V : M.Walk k => V.x 0 = u ∧ V.x ⟨k, Nat.lt_succ_self k⟩ = u) ⟨C, hCs, hCe⟩
    have hw : IsLeast {y : ℝ | ∃ V : M.Walk l,
        V.x 0 = s₀ ∧ (∃ t : Fin (l+1), V.x t = u) ∧ y = V.cost} Pmin.cost := by
      refine ⟨⟨Pmin, hPm.1, hPm.2, rfl⟩, ?_⟩
      rintro y ⟨V, hVs, hv, rfl⟩
      exact hPmin V ⟨hVs, hv⟩
    have hr : IsLeast {y : ℝ | ∃ V : M.Walk k,
        V.x 0 = u ∧ V.x ⟨k, Nat.lt_succ_self k⟩ = u ∧ y = V.cost} Cmin.cost := by
      refine ⟨⟨Cmin, hCm.1, hCm.2, rfl⟩, ?_⟩
      rintro y ⟨V, hVs, hVe, rfl⟩
      exact hCmin V ⟨hVs, hVe⟩
    have hlo := MDPProof.candidate_lower M s₀ T l k u Pmin.cost Cmin.cost hl hd hw hr
    have hupper : Pmin.cost + (((T-l)/k : ℕ) : ℝ) * Cmin.cost ≤ W.cost := by
      rw [hcost]
      exact add_le_add (hPmin P ⟨hPs, hvisit⟩)
        (mul_le_mul_of_nonneg_left (hCmin C ⟨hCs, hCe⟩) (Nat.cast_nonneg _))
    have hWeq : W.cost = M.optHorizon s₀ T := hWmin.unique hleast
    have heq : M.optHorizon s₀ T = Pmin.cost + (((T-l)/k : ℕ) : ℝ) * Cmin.cost :=
      le_antisymm hlo (hupper.trans_eq hWeq)
    exact ⟨l, k, u, Pmin.cost, Cmin.cost, hl, hbound, hkpos, hkbound, hd, hw, hr, heq⟩
  · rintro x ⟨l, k, u, w, r, hl, _, _, _, hd, hw, hr, rfl⟩
    exact MDPProof.candidate_lower M s₀ T l k u w r hl hd hw hr


end MDPComplexity.StationaryHorizon

namespace MDPComplexity.StationaryHorizon

variable {S : Type} [Fintype S]

/-- §3, p. 447, identity underlying Theorem 5: minimize over a short prefix through
`u` and a repeated closed `k`-walk at `u`. The minima in each component are genuine
walk minima, and the outer optimum remains over all time-dependent policies. -/
theorem solution (M : DetMDP S) (s₀ : S) (T : ℕ)
    (hT : (Fintype.card S) ^ 2 < T) :
    IsLeast
      {x : ℝ | ∃ (l k : ℕ) (u : S) (w r : ℝ),
        l ≤ T ∧ l < (Fintype.card S) ^ 3 ∧
        1 ≤ k ∧ k ≤ Fintype.card S ∧ k ∣ T - l ∧
        IsLeast {y : ℝ | ∃ W : M.Walk l,
          W.x 0 = s₀ ∧ (∃ t : Fin (l + 1), W.x t = u) ∧ y = W.cost} w ∧
        IsLeast {y : ℝ | ∃ C : M.Walk k,
          C.x 0 = u ∧ C.x ⟨k, Nat.lt_succ_self k⟩ = u ∧ y = C.cost} r ∧
        x = w + (((T - l) / k : ℕ) : ℝ) * r}
      (M.optHorizon s₀ T) := by
  exact theorem5_structure M s₀ T hT

end MDPComplexity.StationaryHorizon

-- Global platform entrypoint; original proof above is unchanged.
/-- §3, p. 447, identity underlying Theorem 5: minimize over a short prefix through
`u` and a repeated closed `k`-walk at `u`. The minima in each component are genuine
walk minima, and the outer optimum remains over all time-dependent policies. -/
theorem solution {S : Type} [Fintype S] (M : DetMDP S) (s₀ : S) (T : ℕ)
    (hT : (Fintype.card S) ^ 2 < T) :
    IsLeast
      {x : ℝ | ∃ (l k : ℕ) (u : S) (w r : ℝ),
        l ≤ T ∧ l < (Fintype.card S) ^ 3 ∧
        1 ≤ k ∧ k ≤ Fintype.card S ∧ k ∣ T - l ∧
        IsLeast {y : ℝ | ∃ W : M.Walk l,
          W.x 0 = s₀ ∧ (∃ t : Fin (l + 1), W.x t = u) ∧ y = W.cost} w ∧
        IsLeast {y : ℝ | ∃ C : M.Walk k,
          C.x 0 = u ∧ C.x ⟨k, Nat.lt_succ_self k⟩ = u ∧ y = C.cost} r ∧
        x = w + (((T - l) / k : ℕ) : ℝ) * r}
      (M.optHorizon s₀ T) := by
  exact theorem5_structure M s₀ T hT
