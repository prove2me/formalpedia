-- Prove2me | solution 1 for NearLinearRSP.TwoResources.inner_completeness
-- status  : ACCEPTED   (prove)
-- author  : @k-variant
-- created : 2026-11-25T10:27:39.304475+00:00
-- url     : https://prove2.me/submissions/fc031c87-3725-43d2-84c6-1913706b8795

import Theorems.Thm_NearLinearRSP_TwoResources_Implementation_initialization_and_expectation_correct

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal ProbabilityTheory
namespace RSP.Tails

theorem mass_nonneg :
  ∀ (r : ℝ≥0) (n : ℕ),
  0 ≤ mass r n :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.1.2.1.2.1.2.2.2.1

theorem mass_hasSum :
  ∀ (r : ℝ≥0),
  HasSum (mass r) 1 :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.1.2.1.2.2.1.1.1

theorem firstMoment_hasSum :
  ∀ (r : ℝ≥0),
  HasSum (fun n : ℕ => mass r n * (n : ℝ)) (r : ℝ) :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.1.2.1.2.2.1.2.1

theorem secondMoment_hasSum :
  ∀ (r : ℝ≥0),
  HasSum (fun n : ℕ => mass r n * (n : ℝ) ^ 2) ((r : ℝ) ^ 2 + (r : ℝ)) :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.1.2.1.2.2.1.2.2.2

theorem completeness_ratio_le :
  ∀ (q ε : ℝ) (k : ℕ) (hk : 0 < k)
    (hq : 0 < q) (hε : 0 < ε) (hε₁ : ε ≤ 1)
    (hsize : 128 * (k : ℝ) ≤ q * ε ^ 2),
  (q / (1 + ε / 2)) / (q - q / (1 + ε / 2)) ^ 2 ≤
      1 / (8 * (k : ℝ)) :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.1.2.2.1.1.1.1.2.2

end RSP.Tails
end

section
set_option autoImplicit false
open NearLinearRSP.TwoResources
namespace RSP.PoissonBridge

theorem lengthRate_nonneg :
  ∀ (A : InnerInput),
  0 ≤ lengthRate A :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.1.2.2.1.2.1.1.1

theorem costRate_nonneg :
  ∀ (A : InnerInput),
  0 ≤ costRate A :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.1.2.2.1.2.1.1.2.1

end RSP.PoissonBridge
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
open scoped NNReal
namespace NearLinearRSP.TwoResources

theorem pathWeight_cons_cons :
  ∀ (w : ℕ → ℕ → ℝ≥0) (a b : ℕ) (P : List ℕ),
  pathWeight w (a :: b :: P) = (w a b : ℝ) + pathWeight w (b :: P) :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.2.1.1.2.1.2.2.2.1

theorem pathWeight_nonneg :
  ∀ (w : ℕ → ℕ → ℝ≥0) (P : List ℕ),
  0 ≤ pathWeight w P :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.2.1.1.2.1.2.2.2.2

end NearLinearRSP.TwoResources
end

section
set_option autoImplicit false
namespace NearLinearRSP.TwoResources

theorem dpValue_buildTable_source :
  ∀ (A : InnerInput) (i j : ℕ)
    (hi : i < tickLimit A) (hj : j < tickLimit A),
  dpValue A (buildTable A) A.I.source i j = 0 :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.2.2.1.1.2.2.1.1

end NearLinearRSP.TwoResources
end

section
set_option autoImplicit false
namespace NearLinearRSP.TwoResources

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

end NearLinearRSP.TwoResources
end

section
set_option autoImplicit false
open scoped NNReal BigOperators
namespace NearLinearRSP.TwoResources.Completeness

private theorem quadratic_nonneg (q M i r : ℝ) (hr : 0 ≤ r) :
    0 ≤ quadratic q M i r := by
  unfold quadratic
  positivity

private theorem quadratic_saturated (q M i r : ℝ) (hM : M < q)
    (hi : q ≤ i) (hr : 0 ≤ r) : 1 ≤ quadratic q M i r := by
  unfold quadratic
  apply (le_div_iff₀ (sq_pos_of_pos (sub_pos.mpr hM))).mpr
  have hx : 0 ≤ i + r - q := by linarith
  nlinarith [sq_nonneg (i + r - q), mul_nonneg (sub_nonneg.mpr hM.le) hx]

private theorem quadratic_initial (q M : ℝ) : quadratic q M 0 M = M / (q - M) ^ 2 := by
  simp [quadratic]

private theorem quadratic_hasSum (q M i r : ℝ) (e : ℝ≥0) :
    HasSum (fun a : ℕ => RSP.Tails.mass e a * quadratic q M (i + a) r)
      (quadratic q M i (r + e)) := by
  have h := ((RSP.Tails.secondMoment_hasSum e).add
    ((RSP.Tails.firstMoment_hasSum e).mul_right (2 * (i + r - M)))).add
      ((RSP.Tails.mass_hasSum e).mul_right (r + (i + r - M) ^ 2))
  convert! h.div_const ((q - M) ^ 2) using 1
  · ext a
    unfold quadratic
    ring
  · unfold quadratic
    ring

private theorem hasSum_nonneg_product {f g : ℕ → ℝ} {x y : ℝ}
    (hf : HasSum f x) (hg : HasSum g y)
    (hf0 : ∀ i, 0 ≤ f i) (hg0 : ∀ i, 0 ≤ g i) :
    HasSum (fun ab : ℕ × ℕ => f ab.1 * g ab.2) (x * y) :=
  hf.mul hg (hf.summable.mul_of_nonneg hg.summable hf0 hg0)

private theorem product_mass_hasSum (e f : ℝ≥0) :
    HasSum (fun ab : ℕ × ℕ => RSP.Tails.mass e ab.1 * RSP.Tails.mass f ab.2) 1 := by
  simpa using hasSum_nonneg_product (RSP.Tails.mass_hasSum e) (RSP.Tails.mass_hasSum f)
    (RSP.Tails.mass_nonneg e) (RSP.Tails.mass_nonneg f)

private theorem quadratic_pair_hasSum (q M N i j r s : ℝ) (e f : ℝ≥0)
    (hr : 0 ≤ r) (hs : 0 ≤ s) :
    HasSum (fun ab : ℕ × ℕ =>
      (RSP.Tails.mass e ab.1 * RSP.Tails.mass f ab.2) *
        (quadratic q M (i + ab.1) r + quadratic q N (j + ab.2) s))
      (quadratic q M i (r + e) + quadratic q N j (s + f)) := by
  have hL := hasSum_nonneg_product (quadratic_hasSum q M i r e)
    (RSP.Tails.mass_hasSum f)
    (fun a => mul_nonneg (RSP.Tails.mass_nonneg e a)
      (quadratic_nonneg q M (i + a) r hr)) (RSP.Tails.mass_nonneg f)
  have hC := hasSum_nonneg_product (RSP.Tails.mass_hasSum e)
    (quadratic_hasSum q N j s f) (RSP.Tails.mass_nonneg e)
    (fun b => mul_nonneg (RSP.Tails.mass_nonneg f b)
      (quadratic_nonneg q N (j + b) s hs))
  convert! hL.add hC using 1
  · ext ab
    ring
  · ring

private theorem rectangle_comparison {α : Type*} (R : Finset α) (p D G : α → ℝ) (bound : ℝ)
    (hp0 : ∀ a, 0 ≤ p a) (hp : HasSum p 1)
    (hG : HasSum (fun a => p a * G a) bound)
    (hin : ∀ a ∈ R, D a ≤ G a) (hout : ∀ a ∉ R, 1 ≤ G a) :
    1 - ∑ a ∈ R, p a + ∑ a ∈ R, p a * D a ≤ bound := by
  classical
  let correction := fun a => if a ∈ R then p a * (1 - D a) else 0
  have hc : HasSum correction (∑ a ∈ R, p a * (1 - D a)) := by
    have hc0 : HasSum correction (∑ a ∈ R, correction a) :=
      hasSum_sum_of_ne_finset_zero (L := SummationFilter.unconditional α)
        (s := R) (f := correction) (fun a ha => by simp [correction, ha])
    simpa [correction] using hc0
  have hsum := hG.add hc
  have hle : 1 ≤ bound + ∑ a ∈ R, p a * (1 - D a) := by
    apply hasSum_le _ hp hsum
    intro a
    by_cases ha : a ∈ R
    · dsimp [correction]
      rw [if_pos ha]
      nlinarith [mul_le_mul_of_nonneg_left (hin a ha) (hp0 a)]
    · dsimp [correction]
      rw [if_neg ha]
      nlinarith [mul_le_mul_of_nonneg_left (hout a ha) (hp0 a)]
  have hid : (∑ a ∈ R, p a * (1 - D a)) =
      (∑ a ∈ R, p a) - ∑ a ∈ R, p a * D a := by
    simp only [mul_sub, mul_one, Finset.sum_sub_distrib]
  rw [hid] at hle
  linarith

private theorem edgeExpectation_le_quadratic (A : InnerInput) (T : Table)
    (u v i j : ℕ) (M N r s : ℝ)
    (hM : M < (tickLimit A : ℝ)) (hN : N < (tickLimit A : ℝ))
    (hr : 0 ≤ r) (hs : 0 ≤ s)
    (hD : ∀ a b : ℕ, dpValue A T u (i + a) (j + b) ≤
      quadratic (tickLimit A) M (i + a) r + quadratic (tickLimit A) N (j + b) s) :
    edgeExpectation A T u v i j ≤
      quadratic (tickLimit A) M i (r + lengthRate A * A.I.length u v) +
      quadratic (tickLimit A) N j (s + costRate A * A.I.cost u v) := by
  let e : ℝ≥0 := ⟨lengthRate A * A.I.length u v,
    mul_nonneg (RSP.PoissonBridge.lengthRate_nonneg A) (A.I.length u v).coe_nonneg⟩
  let f : ℝ≥0 := ⟨costRate A * A.I.cost u v,
    mul_nonneg (RSP.PoissonBridge.costRate_nonneg A) (A.I.cost u v).coe_nonneg⟩
  have he : (e : ℝ) = lengthRate A * A.I.length u v := rfl
  have hf : (f : ℝ) = costRate A * A.I.cost u v := rfl
  have hr' : 0 ≤ r + (e : ℝ) := add_nonneg hr e.coe_nonneg
  have hs' : 0 ≤ s + (f : ℝ) := add_nonneg hs f.coe_nonneg
  unfold edgeExpectation
  split
  · rename_i hsat
    rcases hsat with hi | hj
    · have hL := quadratic_saturated (tickLimit A) M i (r + e) hM
        (by exact_mod_cast hi) hr'
      have hC := quadratic_nonneg (tickLimit A) N j (s + f) hs'
      change 1 ≤ quadratic (tickLimit A) M i (r + e) + quadratic (tickLimit A) N j (s + f)
      linarith
    · have hL := quadratic_nonneg (tickLimit A) M i (r + e) hr'
      have hC := quadratic_saturated (tickLimit A) N j (s + f) hN
        (by exact_mod_cast hj) hs'
      change 1 ≤ quadratic (tickLimit A) M i (r + e) + quadratic (tickLimit A) N j (s + f)
      linarith
  · let R := Finset.range (tickLimit A - i) ×ˢ Finset.range (tickLimit A - j)
    have h := rectangle_comparison R
      (fun ab : ℕ × ℕ => RSP.Tails.mass e ab.1 * RSP.Tails.mass f ab.2)
      (fun ab => dpValue A T u (i + ab.1) (j + ab.2))
      (fun ab => quadratic (tickLimit A) M ((i : ℝ) + ab.1) r +
        quadratic (tickLimit A) N ((j : ℝ) + ab.2) s)
      (quadratic (tickLimit A) M i (r + e) + quadratic (tickLimit A) N j (s + f))
      (fun ab => mul_nonneg (RSP.Tails.mass_nonneg e ab.1) (RSP.Tails.mass_nonneg f ab.2))
      (product_mass_hasSum e f) (quadratic_pair_hasSum _ _ _ _ _ _ _ e f hr hs)
      (fun ab _ => by simpa only [Nat.cast_add] using hD ab.1 ab.2) ?_
    · simpa only [R, Finset.sum_product, RSP.Tails.mass, he, hf,
        edgeMass, ActuarialValuation.poissonCountMass] using h
    · intro ab hab
      have hab' : tickLimit A ≤ i + ab.1 ∨ tickLimit A ≤ j + ab.2 := by
        simp only [R, Finset.mem_product, Finset.mem_range] at hab
        omega
      rcases hab' with hi | hj
      · have hL := quadratic_saturated (tickLimit A) M ((i : ℝ) + ab.1) r hM
          (by exact_mod_cast hi) hr
        have hC := quadratic_nonneg (tickLimit A) N ((j : ℝ) + ab.2) s hs
        linarith
      · have hL := quadratic_nonneg (tickLimit A) M ((i : ℝ) + ab.1) r hr
        have hC := quadratic_saturated (tickLimit A) N ((j : ℝ) + ab.2) s hN
          (by exact_mod_cast hj) hs
        linarith

private theorem quadratic_feasible_mean (A : InnerInput) (M : ℝ)
    (hM : M ≤ (tickLimit A : ℝ) / (1 + A.δ / 2)) :
    quadratic (tickLimit A) M 0 M ≤ 1 / 16 := by
  have hδ := A.accuracy_pos
  have hq : (0 : ℝ) < tickLimit A := by
    have : 0 < tickLimit A := by
      unfold tickLimit
      apply Nat.ceil_pos.mpr
      positivity
    exact_mod_cast this
  have hbase : (tickLimit A : ℝ) / (1 + A.δ / 2) < tickLimit A :=
    div_lt_self hq (by linarith)
  have hgap := sub_pos.mpr hbase
  rw [quadratic_initial]
  apply le_trans (div_le_div₀ (by positivity) hM (sq_pos_of_pos hgap) ?_)
  · have hsize : 128 * (2 : ℝ) ≤ (tickLimit A : ℝ) * A.δ ^ 2 := by
      have hh : 512 ≤ (tickLimit A : ℝ) * A.δ ^ 2 :=
        (div_le_iff₀ (sq_pos_of_pos hδ)).mp (Nat.le_ceil _)
      linarith
    have hh := RSP.Tails.completeness_ratio_le (tickLimit A) A.δ 2 (by norm_num)
      hq hδ A.accuracy_lt_one.le hsize
    norm_num at hh
    exact hh
  · nlinarith [sq_nonneg ((tickLimit A : ℝ) / (1 + A.δ / 2) - M),
      mul_nonneg hgap.le (sub_nonneg.mpr hM)]

private theorem pathWeight_nonneg (w : ℕ → ℕ → ℝ≥0) (P : List ℕ) :
    0 ≤ pathWeight w P := by
  unfold pathWeight
  apply List.sum_nonneg
  intro x hx
  obtain ⟨e, _, rfl⟩ := List.mem_map.mp hx
  exact (w e.1 e.2).coe_nonneg

private theorem pathWeight_cons_cons (w : ℕ → ℕ → ℝ≥0) (a b : ℕ) (P : List ℕ) :
    pathWeight w (a :: b :: P) = w a b + pathWeight w (b :: P) := by
  simp [pathWeight]

private theorem pathWeight_snoc (w : ℕ → ℕ → ℝ≥0) (P : List ℕ) (u v : ℕ)
    (hP : P.getLast? = some u) :
    pathWeight w (P ++ [v]) = pathWeight w P + w u v := by
  induction P with
  | nil => simp at hP
  | cons a P ih =>
      cases P with
      | nil =>
          have : a = u := by simpa using hP
          subst u
          simp [pathWeight]
      | cons b P =>
          have hp : (b :: P).getLast? = some u := by simpa using hP
          simp only [List.cons_append, pathWeight_cons_cons]
          have hh := ih hp
          simp only [List.cons_append] at hh
          rw [hh]
          ring

private theorem path_quadratic_bound (A : InnerInput) (T : Table)
    (hsource : ∀ i j, i < tickLimit A → j < tickLimit A →
      dpValue A T A.I.source i j = 0)
    (hbellman : ∀ u v, (u, v) ∈ A.I.graph.edges → ∀ i j,
      dpValue A T v i j ≤ edgeExpectation A T u v i j)
    (M N : ℝ) (hM : M < (tickLimit A : ℝ)) (hN : N < (tickLimit A : ℝ)) :
    ∀ (P : List ℕ) (t : ℕ), IsPath A.I.graph A.I.source t P → ∀ i j,
      dpValue A T t i j ≤
        quadratic (tickLimit A) M i (lengthRate A * pathWeight A.I.length P) +
        quadratic (tickLimit A) N j (costRate A * pathWeight A.I.cost P) := by
  intro P
  induction P using List.reverseRecOn with
  | nil =>
      intro t hP
      simp [IsPath] at hP
  | append_singleton P v ih =>
      intro t hP i j
      have ht : v = t := by simpa using hP.2.1
      subst t
      by_cases hnil : P = []
      · subst P
        have hv : v = A.I.source := by simpa using hP.1
        subst v
        simp only [List.nil_append, pathWeight, List.tail_cons, List.zip_nil_right,
          List.map_nil, List.sum_nil, mul_zero]
        by_cases hsat : tickLimit A ≤ i ∨ tickLimit A ≤ j
        · have hd : dpValue A T A.I.source i j = 1 := by simp [dpValue, hsat]
          rw [hd]
          rcases hsat with hi | hj
          · have hL := quadratic_saturated (tickLimit A) M i 0 hM
              (by exact_mod_cast hi) (by norm_num)
            have hC := quadratic_nonneg (tickLimit A) N j 0 (by norm_num)
            linarith
          · have hL := quadratic_nonneg (tickLimit A) M i 0 (by norm_num)
            have hC := quadratic_saturated (tickLimit A) N j 0 hN
              (by exact_mod_cast hj) (by norm_num)
            linarith
        · rw [hsource i j (by omega) (by omega)]
          exact add_nonneg (quadratic_nonneg _ _ _ _ (by norm_num))
            (quadratic_nonneg _ _ _ _ (by norm_num))
      · obtain ⟨u, hu⟩ : ∃ u, P.getLast? = some u := by
          apply Option.isSome_iff_exists.mp
          simpa using hnil
        have hprefix : IsPath A.I.graph A.I.source u P := by
          refine ⟨?_, hu, hP.2.2.left_of_append⟩
          simpa [List.head?_append_of_ne_nil P hnil] using hP.1
        have hedge : (u, v) ∈ A.I.graph.edges :=
          (List.isChain_append.mp hP.2.2).2.2 u (by simp [hu]) v (by simp)
        have hr : 0 ≤ lengthRate A * pathWeight A.I.length P :=
          mul_nonneg (RSP.PoissonBridge.lengthRate_nonneg A) (pathWeight_nonneg _ _)
        have hs : 0 ≤ costRate A * pathWeight A.I.cost P :=
          mul_nonneg (RSP.PoissonBridge.costRate_nonneg A) (pathWeight_nonneg _ _)
        apply (hbellman u v hedge i j).trans
        have h := edgeExpectation_le_quadratic A T u v i j M N
          (lengthRate A * pathWeight A.I.length P) (costRate A * pathWeight A.I.cost P)
          hM hN hr hs (fun a b => by
            simpa only [Nat.cast_add] using ih u hprefix (i + a) (j + b))
        simpa only [pathWeight_snoc _ P u v hu, mul_add] using h

private theorem inner_completeness_of_bellman (A : InnerInput)
    (hsource : ∀ i j, i < tickLimit A → j < tickLimit A →
      dpValue A (buildTable A) A.I.source i j = 0)
    (hbellman : ∀ u v, (u, v) ∈ A.I.graph.edges → ∀ i j,
      dpValue A (buildTable A) v i j ≤ edgeExpectation A (buildTable A) u v i j)
    (t : ℕ) (P : List ℕ) (hP : IsPath A.I.graph A.I.source t P)
    (hL : pathWeight A.I.length P ≤ A.L)
    (hC : pathWeight A.I.cost P ≤ A.I.budget) : accepted A t := by
  let M := lengthRate A * pathWeight A.I.length P
  let N := costRate A * pathWeight A.I.cost P
  have hδ := A.accuracy_pos
  have hhalf : 0 < 1 + A.δ / 2 := by linarith
  have hLpos := A.length_pos
  have hCpos := A.budget_pos
  have hM : M ≤ (tickLimit A : ℝ) / (1 + A.δ / 2) := by
    calc
      M ≤ lengthRate A * A.L :=
        mul_le_mul_of_nonneg_left hL (RSP.PoissonBridge.lengthRate_nonneg A)
      _ = _ := by unfold lengthRate; field_simp
  have hN : N ≤ (tickLimit A : ℝ) / (1 + A.δ / 2) := by
    calc
      N ≤ costRate A * A.I.budget :=
        mul_le_mul_of_nonneg_left hC (RSP.PoissonBridge.costRate_nonneg A)
      _ = _ := by unfold costRate; field_simp
  have hq : (0 : ℝ) < tickLimit A := by
    have : 0 < tickLimit A := by
      unfold tickLimit
      apply Nat.ceil_pos.mpr
      positivity
    exact_mod_cast this
  have hbase : (tickLimit A : ℝ) / (1 + A.δ / 2) < tickLimit A :=
    div_lt_self hq (by linarith)
  have hbound := path_quadratic_bound A (buildTable A) hsource hbellman M N
    (hM.trans_lt hbase) (hN.trans_lt hbase) P t hP 0 0
  have hML := quadratic_feasible_mean A M hM
  have hNC := quadratic_feasible_mean A N hN
  unfold accepted
  have hbound' : dpValue A (buildTable A) t 0 0 ≤ quadratic (tickLimit A) M 0 M +
      quadratic (tickLimit A) N 0 N := by
    simpa only [Nat.cast_zero] using hbound
  linarith

private theorem inner_completeness_of_edge_bounds (A : InnerInput)
    (hbellman : ∀ u v, (u, v) ∈ A.I.graph.edges → ∀ i j,
      dpValue A (buildTable A) v i j ≤ edgeExpectation A (buildTable A) u v i j)
    (t : ℕ) (P : List ℕ) (hP : IsPath A.I.graph A.I.source t P)
    (hL : pathWeight A.I.length P ≤ A.L)
    (hC : pathWeight A.I.cost P ≤ A.I.budget) : accepted A t :=
  inner_completeness_of_bellman A (dpValue_buildTable_source A) hbellman t P hP hL hC

end NearLinearRSP.TwoResources.Completeness
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

theorem solution (A : InnerInput) (t : ℕ) (ht : t < A.I.graph.n)
    (P : List ℕ) (hP : IsPath A.I.graph A.I.source t P)
    (hL : pathWeight A.I.length P ≤ A.L) (hC : pathWeight A.I.cost P ≤ A.I.budget) :
    accepted A t :=
  Completeness.inner_completeness_of_edge_bounds A
    (dpValue_buildTable_le_edgeExpectation A) t P hP hL hC
