-- Prove2me | solution 1 for NearLinearRSP.TwoResources.dp_faithfulness
-- status  : ACCEPTED   (prove)
-- author  : @k-variant
-- created : 2026-11-25T10:41:39.277073+00:00
-- url     : https://prove2.me/submissions/22103285-801a-4525-a694-c613dde9ca3b

import Theorems.Thm_NearLinearRSP_TwoResources_Implementation_initialization_and_expectation_correct

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

section
set_option autoImplicit false
namespace NearLinearRSP.TwoResources

theorem firstMin_mem :
  ∀ {α : Type} (f : α → ℝ) (xs : List α) (fallback : α)
    (h : xs ≠ []),
  firstMin f xs fallback ∈ xs :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.1.1.1.2.1.2.1.2.2

theorem dp_faithfulness_saturated :
  ∀ (A : InnerInput) (T : Table) (u v i j : ℕ)
    (h : tickLimit A ≤ i ∨ tickLimit A ≤ j),
  dpValue A T v i j = edgeExpectation A T u v i j :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.1.1.1.2.1.2.2.1.1

end NearLinearRSP.TwoResources
end

section
namespace NearLinearRSP.TwoResources
open scoped BigOperators

theorem dpValue_range :
  ∀ (A : InnerInput) (T : Table) (hT : TableRange T)
    (v i j : ℕ),
  0 ≤ dpValue A T v i j ∧ dpValue A T v i j ≤ 1 :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.1.2.2.1.2.2.2.2.2

theorem initLayer_range :
  ∀ (A : InnerInput) (T : Table) (hT : TableRange T)
    (i j : ℕ),
  LayerRange (initLayer A T i j) :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.1.2.2.2.1.1.1.2.1

theorem buildLayer_range :
  ∀ (A : InnerInput) (T : Table) (hT : TableRange T)
    (i j : ℕ),
  TableRange (buildLayer A T i j) :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.1.2.2.2.1.1.2.2.1

theorem dpValue_buildTable_nonneg :
  ∀ (A : InnerInput) (v i j : ℕ),
  0 ≤ dpValue A (buildTable A) v i j :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.1.2.2.2.1.2.1.1

end NearLinearRSP.TwoResources
end

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

@[simp] theorem putCell_same :
  ∀ (T : Table) (v i j : ℕ) (c : Cell),
  putCell T v i j c v i j = c :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.1.2.2.2.1.2.2.1.2

theorem putCell_other_vertex :
  ∀ (T : Table) (v w i j : ℕ) (c : Cell) (h : w ≠ v),
  putCell T v i j c w i j = T w i j :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.1.2.2.2.1.2.2.2.1

@[simp] theorem relaxEdge_table :
  ∀ (A : InnerInput) (i j u : ℕ) (S : LayerState)
    (e : ℕ × ℕ),
  (relaxEdge A i j u S e).table = S.table :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.1.2.2.2.2.1.1.1

@[simp] theorem relaxEdge_queue :
  ∀ (A : InnerInput) (i j u : ℕ) (S : LayerState)
    (e : ℕ × ℕ),
  (relaxEdge A i j u S e).queue = S.queue :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.1.2.2.2.2.1.1.2.1

theorem relaxEdge_keys_le :
  ∀ (A : InnerInput) (i j u v : ℕ) (S : LayerState)
    (e : ℕ × ℕ),
  (relaxEdge A i j u S e).keys v ≤ S.keys v :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.1.2.2.2.2.1.2.2.1

@[simp] theorem relaxAll_table :
  ∀ (A : InnerInput) (i j u : ℕ) (S : LayerState),
  (relaxAll A i j u S).table = S.table :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.1.2.2.2.2.2.1.1

@[simp] theorem relaxAll_queue :
  ∀ (A : InnerInput) (i j u : ℕ) (S : LayerState),
  (relaxAll A i j u S).queue = S.queue :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.1.2.2.2.2.2.1.2.1

theorem relaxAll_keys_outside :
  ∀ (A : InnerInput) (i j u v : ℕ) (S : LayerState)
    (hv : v ∉ S.queue),
  (relaxAll A i j u S).keys v = S.keys v :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.1.2.2.2.2.2.2.1.1

theorem relaxAll_parents_outside :
  ∀ (A : InnerInput) (i j u v : ℕ) (S : LayerState)
    (hv : v ∉ S.queue),
  (relaxAll A i j u S).parents v = S.parents v :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.1.2.2.2.2.2.2.1.2

@[simp] theorem queueRun_succ :
  ∀ (A : InnerInput) (i j n : ℕ) (S : LayerState),
  queueRun A i j (n + 1) S = popLayer A i j (queueRun A i j n S) :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.2.1.1.1.1.1.1.2.2

theorem buildLayer_other_layer :
  ∀ (A : InnerInput) (T : Table) (i j v a b : ℕ)
    (h : a ≠ i ∨ b ≠ j),
  buildLayer A T i j v a b = T v a b :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.2.1.1.1.1.2.1.1

theorem buildLayer_queue_exhausted :
  ∀ (A : InnerInput) (T : Table) (i j : ℕ),
  (queueRun A i j (activeVertices A.I).length (initLayer A T i j)).queue = [] :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.2.1.1.1.1.2.1.2.1

theorem queueRun_queue_nodup :
  ∀ (A : InnerInput) (i j n : ℕ) (S : LayerState)
    (h : S.queue.Nodup),
  (queueRun A i j n S).queue.Nodup :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.2.1.1.1.1.2.2.1.1

theorem queueRun_sync :
  ∀ (A : InnerInput) (i j n : ℕ) (S : LayerState)
    (hdup : S.queue.Nodup) (hS : PoppedSync A i j S),
  PoppedSync A i j (queueRun A i j n S) :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.2.1.1.1.1.2.2.2.1

theorem queueRun_range :
  ∀ (A : InnerInput) (i j n : ℕ) (S : LayerState)
    (hS : LayerRange S),
  LayerRange (queueRun A i j n S) :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.2.1.1.1.2.1.1.2.2

theorem edgeExpectation_congr :
  ∀ (A : InnerInput) (T U : Table) (u v i j : ℕ)
    (h : ∀ a ∈ Finset.range (tickLimit A - i),
      ∀ b ∈ Finset.range (tickLimit A - j),
        dpValue A T u (i + a) (j + b) = dpValue A U u (i + a) (j + b)),
  edgeExpectation A T u v i j = edgeExpectation A U u v i j :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.2.1.1.1.2.1.2.2.2

theorem dpValue_congr_at :
  ∀ (A : InnerInput) (T U : Table) (v i j : ℕ)
    (h : T v i j = U v i j),
  dpValue A T v i j = dpValue A U v i j :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.2.1.1.1.2.2.1.2.2

theorem popLayer_keys_le :
  ∀ (A : InnerInput) (i j v : ℕ) (S : LayerState),
  (popLayer A i j S).keys v ≤ S.keys v :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.2.1.1.1.2.2.2.2.2

theorem queueRun_futureBound :
  ∀ (A : InnerInput) (i j n : ℕ) (S : LayerState)
    (hS : LayerFutureBound A i j S),
  LayerFutureBound A i j (queueRun A i j n S) :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.2.1.1.2.1.1.1.2.2

theorem settleState_expectation_ge :
  ∀ (A : InnerInput) (i j u : ℕ) (S : LayerState)
    (hi : i < tickLimit A) (hj : j < tickLimit A) (hu : u ∈ S.queue)
    (hS : LayerRange S) (hfuture : LayerFutureBound A i j S) (v : ℕ),
  S.keys u ≤ edgeExpectation A (settleState S i j u).table u v i j :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.2.1.1.2.1.1.2.1

theorem pickedVertex_mem :
  ∀ (S : LayerState) (hne : S.queue ≠ []),
  pickedVertex S ∈ S.queue :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.2.1.1.2.1.2.1.1

theorem popLayer_eq_relaxAll :
  ∀ (A : InnerInput) (i j : ℕ) (S : LayerState)
    (hne : S.queue ≠ []),
  popLayer A i j S =
      relaxAll A i j (pickedVertex S) (settleState S i j (pickedVertex S)) :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.2.1.1.2.1.2.1.2.2

theorem popLayer_keys_ge_picked :
  ∀ (A : InnerInput) (i j : ℕ) (S : LayerState)
    (hi : i < tickLimit A) (hj : j < tickLimit A) (hne : S.queue ≠ [])
    (hS : LayerRange S) (hfuture : LayerFutureBound A i j S),
  ∀ v ∈ (popLayer A i j S).queue,
      S.keys (pickedVertex S) ≤ (popLayer A i j S).keys v :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.2.1.1.2.1.2.2.1.1

end NearLinearRSP.TwoResources
end

section
set_option autoImplicit false
namespace NearLinearRSP.TwoResources

private theorem foldl_preserves_property {α β : Type*} (f : β → α → β) (P : β → Prop)
    (xs : List α) (b : β) (hb : P b)
    (hf : ∀ a ∈ xs, ∀ b, P b → P (f b a)) : P (xs.foldl f b) := by
  induction xs generalizing b with
  | nil => exact hb
  | cons a xs ih =>
      apply ih (f b a) (hf a (by simp) b hb)
      intro c hc U hU
      exact hf c (by simp [hc]) U hU

private theorem putCell_parentsSupported (A : InnerInput) (T : Table) (v i j : ℕ) (c : Cell)
    (hT : TableParentsSupported A T) (hc : ParentSupported A v c.parent) :
    TableParentsSupported A (putCell T v i j c) := by
  intro w a b
  unfold putCell
  split
  · rename_i h
    rcases h with ⟨rfl, rfl, rfl⟩
    exact hc
  · exact hT w a b

private theorem initLayer_parentsSupported (A : InnerInput) (T : Table) (i j : ℕ)
    (hT : TableParentsSupported A T) : LayerParentsSupported A (initLayer A T i j) := by
  refine ⟨hT, ?_⟩
  intro v
  change ParentSupported A v (if v = A.I.source then Parent.none else
    if dpValue A T v (i+1) j ≤ dpValue A T v i (j+1) then .lengthTick else .costTick)
  split
  · assumption
  · split <;> trivial

private theorem relaxEdge_parentsSupported (A : InnerInput) (i j u : ℕ) (S : LayerState)
    (e : ℕ × ℕ) (hS : LayerParentsSupported A S) (he : e ∈ A.I.graph.edges) :
    LayerParentsSupported A (relaxEdge A i j u S e) := by
  unfold relaxEdge
  dsimp only
  split
  · rename_i hguard
    split
    · refine ⟨hS.1, ?_⟩
      intro v
      change ParentSupported A v (Function.update S.parents e.2 (.edge u) v)
      by_cases hv : v = e.2
      · subst v
        simp only [Function.update_self]
        change (u,e.2) ∈ A.I.graph.edges
        simpa [← hguard.1] using he
      · simpa [Function.update_of_ne hv] using hS.2 v
    · exact hS
  · exact hS

private theorem popLayer_parentsSupported (A : InnerInput) (i j : ℕ) (S : LayerState)
    (hS : LayerParentsSupported A S) : LayerParentsSupported A (popLayer A i j S) := by
  unfold popLayer
  split
  · exact hS
  · apply foldl_preserves_property
    · exact ⟨putCell_parentsSupported A S.table _ i j _ hS.1 (hS.2 _), hS.2⟩
    · intro e he U hU
      exact relaxEdge_parentsSupported A i j _ U e hU he

private theorem buildLayer_parentsSupported (A : InnerInput) (T : Table) (i j : ℕ)
    (hT : TableParentsSupported A T) : TableParentsSupported A (buildLayer A T i j) := by
  exact (foldl_preserves_property (fun S _ => popLayer A i j S) (LayerParentsSupported A)
    (List.range (activeVertices A.I).length) (initLayer A T i j)
    (initLayer_parentsSupported A T i j hT)
    (fun _ _ S hS => popLayer_parentsSupported A i j S hS)).1

private theorem buildTable_parentsSupported (A : InnerInput) :
    TableParentsSupported A (buildTable A) := by
  unfold buildTable
  apply foldl_preserves_property
  · intro v i j
    trivial
  · intro i _ T hT
    apply foldl_preserves_property
    · exact hT
    · intro j _ U hU
      exact buildLayer_parentsSupported A U i j hU

private theorem buildTable_parent_edge_mem (A : InnerInput) (v i j u : ℕ)
    (hp : (buildTable A v i j).parent = .edge u) : (u,v) ∈ A.I.graph.edges := by
  have h := buildTable_parentsSupported A v i j
  simpa [hp, ParentSupported] using h

private theorem edgeExpectation_putCell_other (A : InnerInput) (T : Table)
    (w u v i j : ℕ) (c : Cell) (hu : u ≠ w) :
    edgeExpectation A (putCell T w i j c) u v i j = edgeExpectation A T u v i j := by
  simp [edgeExpectation, dpValue, putCell, hu]

private theorem initLayer_edgeConsistency (A : InnerInput) (T : Table) (i j : ℕ) :
    EdgeConsistency A i j (initLayer A T i j) := by
  intro v u hp
  simp only [initLayer] at hp
  split_ifs at hp <;> contradiction

private theorem relaxEdge_edgeConsistency (A : InnerInput) (i j u : ℕ) (S : LayerState)
    (e : ℕ × ℕ) (hu : u ∉ S.queue) (h : EdgeConsistency A i j S) :
    EdgeConsistency A i j (relaxEdge A i j u S e) := by
  unfold relaxEdge
  dsimp only
  split
  · rename_i he
    split
    · intro v p hp
      by_cases hv : v = e.2
      · subst v
        simp only [Function.update_self, Parent.edge.injEq] at hp
        subst p
        exact ⟨hu, by simpa only [Function.update_self, he.1]⟩
      · simp only [Function.update_of_ne hv] at hp ⊢
        exact h v p hp
    · exact h
  · exact h

private theorem relaxAll_edgeConsistency (A : InnerInput) (i j u : ℕ) (S : LayerState)
    (hu : u ∉ S.queue) (h : EdgeConsistency A i j S) :
    EdgeConsistency A i j (relaxAll A i j u S) := by
  unfold relaxAll
  generalize A.I.graph.edges = es
  induction es generalizing S with
  | nil => exact h
  | cons e es ih =>
      rw [List.foldl_cons]
      exact ih _ (by simpa using hu) (relaxEdge_edgeConsistency A i j u S e hu h)

private theorem settleState_edgeConsistency (A : InnerInput) (i j u : ℕ) (S : LayerState)
    (hu : u ∈ S.queue) (h : EdgeConsistency A i j S) :
    EdgeConsistency A i j (settleState S i j u) := by
  intro v p hp
  have hold := h v p hp
  have hpu : p ≠ u := by intro hpu; subst p; exact hold.1 hu
  refine ⟨fun hm => hold.1 (List.mem_of_mem_erase hm), ?_⟩
  change S.keys v = edgeExpectation A (putCell S.table u i j _) p v i j
  rw [edgeExpectation_putCell_other A S.table u p v i j _ hpu]
  exact hold.2

private theorem popLayer_edgeConsistency (A : InnerInput) (i j : ℕ) (S : LayerState)
    (hdup : S.queue.Nodup) (h : EdgeConsistency A i j S) :
    EdgeConsistency A i j (popLayer A i j S) := by
  unfold popLayer
  split
  · exact h
  · rename_i w ws hq
    let u := firstMin S.keys S.queue w
    have hu : u ∈ S.queue := firstMin_mem _ _ _ (by rw [hq]; simp)
    change EdgeConsistency A i j (relaxAll A i j u (settleState S i j u))
    exact relaxAll_edgeConsistency A i j u _ hdup.not_mem_erase
      (settleState_edgeConsistency A i j u S hu h)

private theorem queueRun_edgeConsistency (A : InnerInput) (i j n : ℕ) (S : LayerState)
    (hdup : S.queue.Nodup) (h : EdgeConsistency A i j S) :
    EdgeConsistency A i j (queueRun A i j n S) := by
  induction n with
  | zero => exact h
  | succ n ih =>
      rw [queueRun_succ]
      exact popLayer_edgeConsistency A i j _ (queueRun_queue_nodup A i j n S hdup) ih

private theorem popLayer_parentSync (A : InnerInput) (i j : ℕ) (S : LayerState)
    (h : PoppedParentSync A i j S) : PoppedParentSync A i j (popLayer A i j S) := by
  unfold popLayer
  split
  · exact h
  · rename_i w ws hq
    let u := firstMin S.keys S.queue w
    let U := settleState S i j u
    change PoppedParentSync A i j (relaxAll A i j u U)
    intro v hv hvq
    have hvU : v ∉ U.queue := by simpa only [relaxAll_queue] using hvq
    rw [relaxAll_table, relaxAll_parents_outside A i j u v U hvU]
    change (putCell S.table u i j _ v i j).parent = S.parents v
    by_cases hvu : v = u
    · subst v
      simp
    · rw [putCell_other_vertex _ _ _ _ _ _ hvu]
      apply h v hv
      intro hm
      exact hvU ((List.mem_erase_of_ne hvu).mpr hm)

private theorem queueRun_parentSync (A : InnerInput) (i j n : ℕ) (S : LayerState)
    (h : PoppedParentSync A i j S) : PoppedParentSync A i j (queueRun A i j n S) := by
  induction n with
  | zero => exact h
  | succ n ih => rw [queueRun_succ]; exact popLayer_parentSync A i j _ ih

private theorem buildLayer_selected_edge (A : InnerInput) (T : Table) (i j v u : ℕ)
    (hv : v ∈ activeVertices A.I) (hp : (buildLayer A T i j v i j).parent = .edge u) :
    (buildLayer A T i j v i j).value = edgeExpectation A (buildLayer A T i j) u v i j := by
  let S := initLayer A T i j
  let n := (activeVertices A.I).length
  have hs : PoppedSync A i j S := by intro v hv hn; exact False.elim (hn hv)
  have hp' : PoppedParentSync A i j S := by intro v hv hn; exact False.elim (hn hv)
  have hsync := queueRun_sync A i j n S (activeVertices_nodup A.I) hs
  have hpsync := queueRun_parentSync A i j n S hp'
  have he := queueRun_edgeConsistency A i j n S (activeVertices_nodup A.I)
    (initLayer_edgeConsistency A T i j)
  have hnot : v ∉ (queueRun A i j n S).queue := by
    rw [buildLayer_queue_exhausted A T i j]; simp
  have hparent : (queueRun A i j n S).parents v = .edge u :=
    (hpsync v hv hnot).symm.trans hp
  exact (hsync v hv hnot).trans (he v u hparent).2

private theorem layerSchedule_mem (A : InnerInput) (i j : ℕ) :
    (i,j) ∈ layerSchedule A ↔ i < tickLimit A ∧ j < tickLimit A := by
  simp [layerSchedule, List.mem_flatMap, List.mem_map]

private theorem layerSchedule_ordered (A : InnerInput) :
    (layerSchedule A).Pairwise layerBefore := by
  have hr : ((List.range (tickLimit A)).reverse).Pairwise
      (fun i j : ℕ => j < i) := by
    simpa only [List.pairwise_reverse] using
      (List.pairwise_lt_range : (List.range (tickLimit A)).Pairwise (· < ·))
  apply List.pairwise_flatMap.mpr
  constructor
  · intro i _
    apply List.pairwise_map.mpr
    exact hr.imp (fun {_ _} hjk => Or.inr ⟨rfl, hjk⟩)
  · apply hr.imp
    intro i j hij x hx y hy
    obtain ⟨a, _, rfl⟩ := List.mem_map.mp hx
    obtain ⟨b, _, rfl⟩ := List.mem_map.mp hy
    exact Or.inl hij

private theorem buildTable_eq_runLayers (A : InnerInput) :
    buildTable A = runLayers A (layerSchedule A) (fun _ _ _ => ⟨1,.lengthTick,0⟩) := by
  simp only [buildTable, runLayers, layerSchedule, List.foldl_flatMap, List.foldl_map]

private theorem runLayers_range (A : InnerInput) (layers : List (ℕ × ℕ)) (T : Table)
    (hT : TableRange T) : TableRange (runLayers A layers T) := by
  induction layers generalizing T with
  | nil => exact hT
  | cons p ps ih => exact ih (buildLayer A T p.1 p.2) (buildLayer_range A T hT _ _)

private theorem runLayers_frame (A : InnerInput) (layers : List (ℕ × ℕ)) (T : Table)
    (v a b : ℕ) (h : ∀ p ∈ layers, a ≠ p.1 ∨ b ≠ p.2) :
    runLayers A layers T v a b = T v a b := by
  induction layers generalizing T with
  | nil => rfl
  | cons p ps ih =>
      change runLayers A ps (buildLayer A T p.1 p.2) v a b = T v a b
      rw [ih _ (fun p hp => h p (by simp [hp]))]
      exact buildLayer_other_layer A T p.1 p.2 v a b (h p (by simp))

private theorem buildTable_layer_witness (A : InnerInput) (i j : ℕ)
    (hi : i < tickLimit A) (hj : j < tickLimit A) :
    ∃ T : Table, TableRange T ∧
      ∀ v a b, (i < a ∨ i = a ∧ j ≤ b) →
        buildTable A v a b = buildLayer A T i j v a b := by
  have hm := (layerSchedule_mem A i j).mpr ⟨hi,hj⟩
  obtain ⟨pre, post, hs⟩ := List.mem_iff_append.mp hm
  let T : Table := runLayers A pre (fun _ _ _ => ⟨1,.lengthTick,0⟩)
  refine ⟨T, runLayers_range A pre _ (by intro v a b; exact ⟨zero_le_one,le_rfl⟩), ?_⟩
  intro v a b hab
  have hord := layerSchedule_ordered A
  rw [hs] at hord
  have hpost : ∀ p ∈ post, layerBefore (i,j) p :=
    (List.pairwise_cons.mp (List.pairwise_append.mp hord).2.1).1
  rw [buildTable_eq_runLayers, hs]
  change ((pre ++ (i,j) :: post).foldl
    (fun U p => buildLayer A U p.1 p.2) (fun _ _ _ => ⟨1,.lengthTick,0⟩)) v a b = _
  rw [List.foldl_append, List.foldl_cons]
  apply runLayers_frame A post (buildLayer A T i j) v a b
  intro p hp
  have hh := hpost p hp
  dsimp [layerBefore] at hh
  omega

private theorem dpValue_buildTable_selected_edge (A : InnerInput) (v i j u : ℕ)
    (hp : (buildTable A v i j).parent = .edge u) :
    dpValue A (buildTable A) v i j = edgeExpectation A (buildTable A) u v i j := by
  by_cases hs : tickLimit A ≤ i ∨ tickLimit A ≤ j
  · exact dp_faithfulness_saturated A (buildTable A) u v i j hs
  have hi : i < tickLimit A := by omega
  have hj : j < tickLimit A := by omega
  have hv : v ∈ activeVertices A.I :=
    activeVertices_edge_right A.I u v (buildTable_parent_edge_mem A v i j u hp)
  obtain ⟨T, _, hfinal⟩ := buildTable_layer_witness A i j hi hj
  have hhere := hfinal v i j (Or.inr ⟨rfl, le_rfl⟩)
  have hparent : (buildLayer A T i j v i j).parent = .edge u := by
    rw [← hhere]; exact hp
  have he := buildLayer_selected_edge A T i j v u hv hparent
  have hexp : edgeExpectation A (buildTable A) u v i j =
      edgeExpectation A (buildLayer A T i j) u v i j := by
    apply edgeExpectation_congr
    intro a _ b _
    apply dpValue_congr_at
    apply hfinal
    omega
  rw [hexp]
  simpa only [dpValue, if_neg hs, hhere] using he

end NearLinearRSP.TwoResources
end

section
set_option autoImplicit false
namespace NearLinearRSP.TwoResources

private theorem queueRun_keys_le (A : InnerInput) (i j n v : ℕ) (S : LayerState) :
    (queueRun A i j n S).keys v ≤ S.keys v := by
  induction n with
  | zero => exact le_rfl
  | succ n ih =>
      rw [queueRun_succ]
      exact (popLayer_keys_le A i j v _).trans ih

private theorem buildLayer_value_le_initial (A : InnerInput) (T : Table) (i j v : ℕ)
    (hv : v ∈ activeVertices A.I) :
    (buildLayer A T i j v i j).value ≤ (initLayer A T i j).keys v := by
  have hsync : PoppedSync A i j (initLayer A T i j) := by
    intro w hw hwq
    exact False.elim (hwq hw)
  have h := queueRun_sync A i j (activeVertices A.I).length (initLayer A T i j)
    (activeVertices_nodup A.I) hsync
  have hempty := buildLayer_queue_exhausted A T i j
  have heq := h v hv (by rw [hempty]; simp)
  exact heq.le.trans (queueRun_keys_le A i j (activeVertices A.I).length v _)

private theorem buildLayer_value_le_next_length (A : InnerInput) (T : Table) (i j v : ℕ)
    (hT : TableRange T) (hv : v ∈ activeVertices A.I) :
    (buildLayer A T i j v i j).value ≤ dpValue A T v (i + 1) j := by
  apply (buildLayer_value_le_initial A T i j v hv).trans
  change (if v = A.I.source then 0 else
    min (dpValue A T v (i + 1) j) (dpValue A T v i (j + 1))) ≤ _
  split
  · exact (dpValue_range A T hT v (i + 1) j).1
  · exact min_le_left _ _

private theorem buildLayer_value_le_next_cost (A : InnerInput) (T : Table) (i j v : ℕ)
    (hT : TableRange T) (hv : v ∈ activeVertices A.I) :
    (buildLayer A T i j v i j).value ≤ dpValue A T v i (j + 1) := by
  apply (buildLayer_value_le_initial A T i j v hv).trans
  change (if v = A.I.source then 0 else
    min (dpValue A T v (i + 1) j) (dpValue A T v i (j + 1))) ≤ _
  split
  · exact (dpValue_range A T hT v i (j + 1)).1
  · exact min_le_right _ _

private theorem dpValue_buildTable_le_next_length (A : InnerInput) (v i j : ℕ)
    (hv : v ∈ activeVertices A.I) :
    dpValue A (buildTable A) v i j ≤ dpValue A (buildTable A) v (i + 1) j := by
  by_cases hsat : tickLimit A ≤ i ∨ tickLimit A ≤ j
  · have hsat' : tickLimit A ≤ i + 1 ∨ tickLimit A ≤ j := by omega
    simp [dpValue, hsat, hsat']
  · have hi : i < tickLimit A := by omega
    have hj : j < tickLimit A := by omega
    obtain ⟨T, hT, hfinal⟩ := buildTable_layer_witness A i j hi hj
    have hhere : dpValue A (buildTable A) v i j = (buildLayer A T i j v i j).value := by
      simp [dpValue, hsat, hfinal v i j (Or.inr ⟨rfl, le_rfl⟩)]
    have hnext : dpValue A T v (i + 1) j = dpValue A (buildTable A) v (i + 1) j := by
      unfold dpValue
      split
      · rfl
      · rw [hfinal v (i + 1) j (Or.inl (by omega)),
          buildLayer_other_layer A T i j v (i + 1) j (Or.inl (by omega))]
    rw [hhere, ← hnext]
    exact buildLayer_value_le_next_length A T i j v hT hv

private theorem dpValue_buildTable_le_next_cost (A : InnerInput) (v i j : ℕ)
    (hv : v ∈ activeVertices A.I) :
    dpValue A (buildTable A) v i j ≤ dpValue A (buildTable A) v i (j + 1) := by
  by_cases hsat : tickLimit A ≤ i ∨ tickLimit A ≤ j
  · have hsat' : tickLimit A ≤ i ∨ tickLimit A ≤ j + 1 := by omega
    simp [dpValue, hsat, hsat']
  · have hi : i < tickLimit A := by omega
    have hj : j < tickLimit A := by omega
    obtain ⟨T, hT, hfinal⟩ := buildTable_layer_witness A i j hi hj
    have hhere : dpValue A (buildTable A) v i j = (buildLayer A T i j v i j).value := by
      simp [dpValue, hsat, hfinal v i j (Or.inr ⟨rfl, le_rfl⟩)]
    have hnext : dpValue A T v i (j + 1) = dpValue A (buildTable A) v i (j + 1) := by
      unfold dpValue
      split
      · rfl
      · rw [hfinal v i (j + 1) (Or.inr ⟨rfl, by omega⟩),
          buildLayer_other_layer A T i j v i (j + 1) (Or.inr (by omega))]
    rw [hhere, ← hnext]
    exact buildLayer_value_le_next_cost A T i j v hT hv

private theorem dpValue_buildTable_monotone_length (A : InnerInput) (v j : ℕ)
    (hv : v ∈ activeVertices A.I) :
    Monotone (fun i => dpValue A (buildTable A) v i j) :=
  monotone_nat_of_le_succ (fun i => dpValue_buildTable_le_next_length A v i j hv)

private theorem dpValue_buildTable_monotone_cost (A : InnerInput) (v i : ℕ)
    (hv : v ∈ activeVertices A.I) :
    Monotone (fun j => dpValue A (buildTable A) v i j) :=
  monotone_nat_of_le_succ (fun j => dpValue_buildTable_le_next_cost A v i j hv)

private theorem dpValue_buildTable_mono (A : InnerInput) (v i j a b : ℕ)
    (hv : v ∈ activeVertices A.I) (hi : i ≤ a) (hj : j ≤ b) :
    dpValue A (buildTable A) v i j ≤ dpValue A (buildTable A) v a b :=
  (dpValue_buildTable_monotone_length A v j hv hi).trans
    (dpValue_buildTable_monotone_cost A v a hv hj)

private theorem popLayer_keys_outside (A : InnerInput) (i j v : ℕ) (S : LayerState)
    (hv : v ∉ S.queue) : (popLayer A i j S).keys v = S.keys v := by
  by_cases hne : S.queue = []
  · simp [popLayer, hne]
  · rw [popLayer_eq_relaxAll A i j S hne]
    apply relaxAll_keys_outside
    intro hm
    exact hv (List.mem_of_mem_erase hm)

private theorem popLayer_key_picked (A : InnerInput) (i j : ℕ) (S : LayerState)
    (hne : S.queue ≠ []) (hdup : S.queue.Nodup) :
    (popLayer A i j S).keys (pickedVertex S) = S.keys (pickedVertex S) := by
  rw [popLayer_eq_relaxAll A i j S hne]
  exact relaxAll_keys_outside A i j _ _ _ hdup.not_mem_erase

private theorem popLayer_expectation_other_vertex (A : InnerInput) (i j u v : ℕ)
    (S : LayerState) (hne : S.queue ≠ []) (hu : u ≠ pickedVertex S) :
    edgeExpectation A (popLayer A i j S).table u v i j =
      edgeExpectation A S.table u v i j := by
  rw [popLayer_eq_relaxAll A i j S hne, relaxAll_table]
  apply edgeExpectation_congr
  intro a _ b _
  apply dpValue_congr_at
  simp [settleState, putCell, hu]

private theorem relaxEdge_edge_bound (A : InnerInput) (i j u v : ℕ) (S : LayerState)
    (huv : u ≠ v) (hv : v ∈ S.queue) :
    (relaxEdge A i j u S (u, v)).keys v ≤ edgeExpectation A S.table u v i j := by
  unfold relaxEdge
  rw [if_pos ⟨rfl, huv, hv⟩]
  dsimp only
  split
  · simp
  · rename_i h
    exact le_of_not_gt h

private theorem relaxFold_keys_le_initial (A : InnerInput) (i j u v : ℕ)
    (es : List (ℕ × ℕ)) (S : LayerState) :
    (es.foldl (relaxEdge A i j u) S).keys v ≤ S.keys v := by
  induction es generalizing S with
  | nil => exact le_rfl
  | cons e es ih =>
      rw [List.foldl_cons]
      exact (ih _).trans (relaxEdge_keys_le A i j u v S e)

private theorem relaxAll_edge_bound (A : InnerInput) (i j u v : ℕ) (S : LayerState)
    (huv : u ≠ v) (hv : v ∈ S.queue) (hedge : (u, v) ∈ A.I.graph.edges) :
    (relaxAll A i j u S).keys v ≤ edgeExpectation A S.table u v i j := by
  unfold relaxAll
  generalize he : A.I.graph.edges = es at hedge ⊢
  clear he
  induction es generalizing S with
  | nil => simp at hedge
  | cons e es ih =>
      rw [List.foldl_cons]
      rcases List.mem_cons.mp hedge with he | hm
      · subst e
        exact (relaxFold_keys_le_initial A i j u v es _).trans
          (relaxEdge_edge_bound A i j u v S huv hv)
      · have hrec := ih (relaxEdge A i j u S e) (by simpa using hv) hm
        simpa only [relaxEdge_table] using hrec

private theorem popLayer_separation (A : InnerInput) (i j : ℕ) (S : LayerState)
    (hi : i < tickLimit A) (hj : j < tickLimit A) (hdup : S.queue.Nodup)
    (hS : LayerRange S) (hfuture : LayerFutureBound A i j S)
    (hsep : SettledSeparation A S) : SettledSeparation A (popLayer A i j S) := by
  by_cases hne : S.queue = []
  · simpa [popLayer, hne] using hsep
  · intro u hu huq v hvq
    have hp := pickedVertex_mem S hne
    have hvbound := popLayer_keys_ge_picked A i j S hi hj hne hS hfuture v hvq
    by_cases hup : u = pickedVertex S
    · subst u
      rw [popLayer_key_picked A i j S hne hdup]
      exact hvbound
    · have huold : u ∉ S.queue := by
        intro hm
        apply huq
        rw [popLayer_eq_relaxAll A i j S hne, relaxAll_queue]
        exact (List.mem_erase_of_ne hup).mpr hm
      rw [popLayer_keys_outside A i j u S huold]
      exact (hsep u hu huold _ hp).trans hvbound

private theorem popLayer_bellman (A : InnerInput) (i j : ℕ) (S : LayerState)
    (hi : i < tickLimit A) (hj : j < tickLimit A) (hdup : S.queue.Nodup)
    (hS : LayerRange S) (hfuture : LayerFutureBound A i j S)
    (hsep : SettledSeparation A S) (hbell : SettledBellman A i j S) :
    SettledBellman A i j (popLayer A i j S) := by
  by_cases hne : S.queue = []
  · simpa [popLayer, hne] using hbell
  · intro u hu huq v huv
    have hp := pickedVertex_mem S hne
    have hpop := popLayer_eq_relaxAll A i j S hne
    have htable : (popLayer A i j S).table =
        (settleState S i j (pickedVertex S)).table := by rw [hpop, relaxAll_table]
    by_cases hup : u = pickedVertex S
    · subst u
      rw [htable]
      have hext := settleState_expectation_ge A i j (pickedVertex S) S hi hj hp hS hfuture v
      by_cases hvnew : v ∈ (popLayer A i j S).queue
      · have hvU : v ∈ (settleState S i j (pickedVertex S)).queue := by
          simpa only [hpop, relaxAll_queue] using hvnew
        have hpv : pickedVertex S ≠ v := by
          intro heq
          subst v
          exact hdup.not_mem_erase hvU
        rw [hpop]
        exact relaxAll_edge_bound A i j _ v _ hpv hvU huv
      · by_cases hvp : v = pickedVertex S
        · subst v
          rw [popLayer_key_picked A i j S hne hdup]
          exact hext
        · have hvold : v ∉ S.queue := by
            intro hm
            apply hvnew
            rw [hpop, relaxAll_queue]
            exact (List.mem_erase_of_ne hvp).mpr hm
          rw [popLayer_keys_outside A i j v S hvold]
          exact (hsep v (activeVertices_edge_right A.I _ v huv) hvold _ hp).trans hext
    · have huold : u ∉ S.queue := by
        intro hm
        apply huq
        rw [hpop, relaxAll_queue]
        exact (List.mem_erase_of_ne hup).mpr hm
      rw [popLayer_expectation_other_vertex A i j u v S hne hup]
      exact (popLayer_keys_le A i j v S).trans (hbell u hu huold v huv)

private theorem queueRun_bellman_separation (A : InnerInput) (i j n : ℕ) (S : LayerState)
    (hi : i < tickLimit A) (hj : j < tickLimit A) (hdup : S.queue.Nodup)
    (hS : LayerRange S) (hfuture : LayerFutureBound A i j S)
    (hsep : SettledSeparation A S) (hbell : SettledBellman A i j S) :
    SettledSeparation A (queueRun A i j n S) ∧
      SettledBellman A i j (queueRun A i j n S) := by
  induction n with
  | zero => exact ⟨hsep, hbell⟩
  | succ n ih =>
      rw [queueRun_succ]
      have hdup' := queueRun_queue_nodup A i j n S hdup
      have hrange' := queueRun_range A i j n S hS
      have hfut' := queueRun_futureBound A i j n S hfuture
      exact ⟨popLayer_separation A i j _ hi hj hdup' hrange' hfut' ih.1,
        popLayer_bellman A i j _ hi hj hdup' hrange' hfut' ih.1 ih.2⟩

private theorem buildLayer_edge_le (A : InnerInput) (T : Table) (i j : ℕ)
    (hi : i < tickLimit A) (hj : j < tickLimit A) (hT : TableRange T)
    (hfuture : LayerFutureBound A i j (initLayer A T i j))
    (u v : ℕ) (huv : (u, v) ∈ A.I.graph.edges) :
    dpValue A (buildLayer A T i j) v i j ≤
      edgeExpectation A (buildLayer A T i j) u v i j := by
  let S := initLayer A T i j
  let final := queueRun A i j (activeVertices A.I).length S
  have hsep : SettledSeparation A S := by
    intro a ha hnot
    exact False.elim (hnot ha)
  have hbell : SettledBellman A i j S := by
    intro a ha hnot
    exact False.elim (hnot ha)
  have hterminal : final.queue = [] := buildLayer_queue_exhausted A T i j
  have hmain := (queueRun_bellman_separation A i j (activeVertices A.I).length S hi hj
    (activeVertices_nodup A.I) (initLayer_range A T hT i j) hfuture hsep hbell).2
  have hbound := hmain u (activeVertices_edge_left A.I u v huv)
    (by rw [hterminal]; simp) v huv
  have hsync : PoppedSync A i j final := queueRun_sync A i j _ S
    (activeVertices_nodup A.I) (by intro a ha hnot; exact False.elim (hnot ha))
  have hvalue := hsync v (activeVertices_edge_right A.I u v huv)
    (by rw [hterminal]; simp)
  change dpValue A final.table v i j ≤ edgeExpectation A final.table u v i j
  simpa only [dpValue, Nat.not_le.mpr hi, Nat.not_le.mpr hj, or_self, if_false, hvalue] using hbound

private theorem layer_witness_future_eq (A : InnerInput) (T : Table) (i j : ℕ)
    (hfinal : ∀ v a b, (i < a ∨ i = a ∧ j ≤ b) →
      buildTable A v a b = buildLayer A T i j v a b)
    (v a b : ℕ) (hab : a ≠ 0 ∨ b ≠ 0) :
    dpValue A T v (i + a) (j + b) = dpValue A (buildTable A) v (i + a) (j + b) := by
  unfold dpValue
  split
  · rfl
  · rw [hfinal v (i + a) (j + b) (by omega),
      buildLayer_other_layer A T i j v (i + a) (j + b) (by omega)]

private theorem layer_witness_futureBound (A : InnerInput) (T : Table) (i j : ℕ)
    (hfinal : ∀ v a b, (i < a ∨ i = a ∧ j ≤ b) →
      buildTable A v a b = buildLayer A T i j v a b) :
    LayerFutureBound A i j (initLayer A T i j) := by
  intro v hv a b hab
  have hv' : v ∈ activeVertices A.I := hv
  change (if v = A.I.source then 0 else
    min (dpValue A T v (i + 1) j) (dpValue A T v i (j + 1))) ≤
      dpValue A T v (i + a) (j + b)
  rw [layer_witness_future_eq A T i j hfinal v a b hab]
  split
  · exact dpValue_buildTable_nonneg A v (i + a) (j + b)
  · by_cases ha : a = 0
    · have hb : b ≠ 0 := hab.resolve_left (not_not.mpr ha)
      apply (min_le_right _ _).trans
      have heq := layer_witness_future_eq A T i j hfinal v 0 1 (Or.inr (by omega))
      simp only [Nat.add_zero] at heq
      rw [heq]
      exact dpValue_buildTable_mono A v i (j + 1) (i + a) (j + b) hv' (by omega) (by omega)
    · apply (min_le_left _ _).trans
      have heq := layer_witness_future_eq A T i j hfinal v 1 0 (Or.inl (by omega))
      simp only [Nat.add_zero] at heq
      rw [heq]
      exact dpValue_buildTable_mono A v (i + 1) j (i + a) (j + b) hv' (by omega) (by omega)

private theorem dpValue_buildTable_le_edgeExpectation (A : InnerInput) (u v : ℕ)
    (huv : (u, v) ∈ A.I.graph.edges) (i j : ℕ) :
    dpValue A (buildTable A) v i j ≤ edgeExpectation A (buildTable A) u v i j := by
  by_cases hsat : tickLimit A ≤ i ∨ tickLimit A ≤ j
  · simp [dpValue, edgeExpectation, hsat]
  · have hi : i < tickLimit A := by omega
    have hj : j < tickLimit A := by omega
    obtain ⟨T, hT, hfinal⟩ := buildTable_layer_witness A i j hi hj
    have hhere : dpValue A (buildTable A) v i j = dpValue A (buildLayer A T i j) v i j :=
      dpValue_congr_at A _ _ v i j (hfinal v i j (Or.inr ⟨rfl, le_rfl⟩))
    have hedge : edgeExpectation A (buildTable A) u v i j =
        edgeExpectation A (buildLayer A T i j) u v i j := by
      apply edgeExpectation_congr
      intro a _ b _
      apply dpValue_congr_at
      apply hfinal
      omega
    rw [hhere, hedge]
    exact buildLayer_edge_le A T i j hi hj hT (layer_witness_futureBound A T i j hfinal) u v huv

end NearLinearRSP.TwoResources
end

open NearLinearRSP.TwoResources

theorem solution (A : InnerInput) :
    ∀ u v : ℕ, (u, v) ∈ A.I.graph.edges → ∀ i j : ℕ,
      dpValue A (buildTable A) v i j ≤ edgeExpectation A (buildTable A) u v i j ∧
      (i < tickLimit A → j < tickLimit A →
        (buildTable A v i j).parent = .edge u →
        dpValue A (buildTable A) v i j = edgeExpectation A (buildTable A) u v i j) := by
  intro u v huv i j
  exact ⟨dpValue_buildTable_le_edgeExpectation A u v huv i j,
    fun _ _ hp => dpValue_buildTable_selected_edge A v i j u hp⟩
