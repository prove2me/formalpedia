-- Prove2me | solution 1 for NearLinearRSP.TwoResources.inner_soundness
-- status  : ACCEPTED   (prove)
-- author  : @k-variant
-- created : 2026-11-25T10:38:31.05566+00:00
-- url     : https://prove2.me/submissions/bb1c710e-86e0-43c3-aae0-d3ad445d0060

import Theorems.Thm_NearLinearRSP_TwoResources_Implementation_initialization_and_expectation_correct

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

section
set_option autoImplicit false
namespace NearLinearRSP.TwoResources

theorem firstMin_le_of_mem :
  ∀ {α : Type} (f : α → ℝ) (xs : List α)
    (fallback y : α) (hy : y ∈ xs),
  f (firstMin f xs fallback) ≤ f y :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.1.1.1.2.1.2.1.1

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
set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal ProbabilityTheory
namespace RSP.Tails

theorem poisson_pgf_hasSum :
  ∀ (r : ℝ≥0) (z : ℝ),
  HasSum (fun n : ℕ => mass r n * z ^ n) (Real.exp ((r : ℝ) * (z - 1))) :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.1.2.1.2.2.1.1.2.1

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

theorem poissonCountMass_nonneg :
  ∀ (r : ℝ) (hr : 0 ≤ r) (n : ℕ),
  0 ≤ ActuarialValuation.poissonCountMass r n :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.1.2.2.1.2.1.1.2.2

theorem poissonCountMass_sum_le_one :
  ∀ (r : ℝ) (hr : 0 ≤ r) (n : ℕ),
  (∑ a ∈ Finset.range n, ActuarialValuation.poissonCountMass r a) ≤ 1 :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.1.2.2.1.2.1.2.2.1

theorem edgeMass_nonneg :
  ∀ (A : InnerInput) (u v a b : ℕ),
  0 ≤ edgeMass A u v a b :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.1.2.2.1.2.1.2.2.2

end RSP.PoissonBridge
end

section
namespace NearLinearRSP.TwoResources
open scoped BigOperators

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

@[simp] theorem relaxEdge_nextRank :
  ∀ (A : InnerInput) (i j u : ℕ) (S : LayerState)
    (e : ℕ × ℕ),
  (relaxEdge A i j u S e).nextRank = S.nextRank :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.1.2.2.2.2.1.1.2.2

@[simp] theorem relaxAll_table :
  ∀ (A : InnerInput) (i j u : ℕ) (S : LayerState),
  (relaxAll A i j u S).table = S.table :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.1.2.2.2.2.2.1.1

@[simp] theorem relaxAll_queue :
  ∀ (A : InnerInput) (i j u : ℕ) (S : LayerState),
  (relaxAll A i j u S).queue = S.queue :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.1.2.2.2.2.2.1.2.1

@[simp] theorem relaxAll_nextRank :
  ∀ (A : InnerInput) (i j u : ℕ) (S : LayerState),
  (relaxAll A i j u S).nextRank = S.nextRank :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.1.2.2.2.2.2.1.2.2

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

end NearLinearRSP.TwoResources
end

section
set_option autoImplicit false
namespace NearLinearRSP.TwoResources

theorem dpValue_buildTable_inactive :
  ∀ (A : InnerInput) (v i j : ℕ)
    (hv : v ∉ activeVertices A.I),
  dpValue A (buildTable A) v i j = 1 :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.2.2.1.2.1.1.1.1

end NearLinearRSP.TwoResources
end

section
set_option autoImplicit false
namespace RSP.Barrier

private theorem log_gap_lower {z : ℝ} (hz : 0 < z) (hz1 : z ≤ 1) :
    (1 - z) ^ 2 / 2 ≤ Real.log z + 1 / z - 1 := by
  let f : ℝ → ℝ := fun x => Real.log x + 1 / x - 1 - (1 - x) ^ 2 / 2
  have hd (x : ℝ) (hx : 0 < x) :
      HasDerivAt f (1 / x - 1 / x ^ 2 + (1 - x)) x := by
    have hlog := Real.hasDerivAt_log (ne_of_gt hx)
    have hinv := (hasDerivAt_id x).inv (ne_of_gt hx)
    have hsq := (((hasDerivAt_id x).const_sub 1).pow 2).div_const 2
    convert! ((hlog.add hinv).sub_const 1).sub hsq using 1
    · ext y
      simp [f, one_div]
    · simp [one_div]
      ring
  have hanti : AntitoneOn f (Set.Icc z 1) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc z 1)
    · intro x hx
      exact (hd x (lt_of_lt_of_le hz hx.1)).continuousAt.continuousWithinAt
    · intro x hx
      exact (hd x (lt_of_lt_of_le hz (interior_subset hx).1)).differentiableAt.differentiableWithinAt
    · intro x hx
      have hx' : x ∈ Set.Icc z 1 := interior_subset hx
      have hx0 : 0 < x := lt_of_lt_of_le hz hx'.1
      rw [(hd x hx0).deriv]
      have heq : (1 / x - 1 / x ^ 2 + (1 - x)) * x ^ 2 =
          -(1 - x) * (1 - x ^ 2) := by
        field_simp [ne_of_gt hx0]
        <;> ring
      have hsq : x ^ 2 ≤ 1 := by nlinarith [hx'.2]
      have hp := mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sub_nonneg.mpr hx'.2))
        (sub_nonneg.mpr hsq)
      rw [← heq] at hp
      nlinarith [sq_pos_of_pos hx0]
  have h := hanti ⟨le_rfl, hz1⟩ ⟨hz1, le_rfl⟩ hz1
  simp only [f, Real.log_one, div_one, sub_self, zero_pow (by decide : 2 ≠ 0),
    zero_div, add_zero, sub_zero] at h
  linarith

private theorem eight_le_clock_barrier {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (q : ℕ) (hq : 512 / δ ^ 2 ≤ (q : ℝ)) :
    let z := (1 + δ / 2) / (1 + δ)
    8 ≤ z ^ (q - 1) * Real.exp ((q : ℝ) * (1 - z) / z) := by
  let z := (1 + δ / 2) / (1 + δ)
  change 8 ≤ z ^ (q - 1) * Real.exp ((q : ℝ) * (1 - z) / z)
  have hd : 0 < 1 + δ := by linarith
  have hz : 0 < z := by dsimp [z]; positivity
  have hz1 : z ≤ 1 := by
    dsimp [z]
    apply (div_le_iff₀ hd).mpr
    linarith
  have hgap : δ / 4 ≤ 1 - z := by
    have heq : 1 - z = (δ / 2) / (1 + δ) := by
      dsimp [z]
      field_simp [ne_of_gt hd]
      <;> ring
    rw [heq]
    apply (le_div_iff₀ hd).mpr
    nlinarith [mul_nonneg (le_of_lt hδ) (sub_nonneg.mpr hδ1)]
  have hlog : δ ^ 2 / 32 ≤ Real.log z + 1 / z - 1 := by
    have h := log_gap_lower hz hz1
    nlinarith [sq_nonneg (1 - z - δ / 4)]
  have hqδ : 512 ≤ (q : ℝ) * δ ^ 2 := (div_le_iff₀ (sq_pos_of_pos hδ)).mp hq
  have hq1r : (1 : ℝ) ≤ q := by
    have hd2 : δ ^ 2 ≤ 1 := by nlinarith
    have hn : (0 : ℝ) ≤ q := Nat.cast_nonneg q
    nlinarith
  have hq1 : 1 ≤ q := by exact_mod_cast hq1r
  have hprod : 16 ≤ (q : ℝ) * (Real.log z + 1 / z - 1) := by
    have hmul := mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg q : (0 : ℝ) ≤ q)
    nlinarith
  have hlog0 : Real.log z ≤ 0 := Real.log_nonpos (le_of_lt hz) hz1
  have hexp : 16 ≤ ((q - 1 : ℕ) : ℝ) * Real.log z + (q : ℝ) * (1 - z) / z := by
    rw [Nat.cast_sub hq1, Nat.cast_one]
    have heq : ((q : ℝ) - 1) * Real.log z + (q : ℝ) * (1 - z) / z =
        (q : ℝ) * (Real.log z + 1 / z - 1) - Real.log z := by
      field_simp
      <;> ring
    rw [heq]
    linarith
  calc
    (8 : ℝ) ≤ Real.exp (16 : ℝ) := by nlinarith [Real.add_one_le_exp (16 : ℝ)]
    _ ≤ Real.exp (((q - 1 : ℕ) : ℝ) * Real.log z + (q : ℝ) * (1 - z) / z) :=
      Real.exp_le_exp.mpr hexp
    _ = z ^ (q - 1) * Real.exp ((q : ℝ) * (1 - z) / z) := by
      rw [Real.exp_add, Real.exp_nat_mul, Real.exp_log hz]

private theorem one_le_resource_term {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (q : ℕ) (hq : 512 / δ ^ 2 ≤ (q : ℝ)) (i : ℕ) (hi : i < q)
    (a : ℝ) (ha : (q : ℝ) / ((1 + δ / 2) / (1 + δ)) ≤ a) :
    let z := (1 + δ / 2) / (1 + δ)
    1 ≤ z ^ i / (8 * Real.exp (a * (z - 1))) := by
  let z := (1 + δ / 2) / (1 + δ)
  change 1 ≤ z ^ i / (8 * Real.exp (a * (z - 1)))
  have hz : 0 < z := by dsimp [z]; positivity
  have hz1 : z ≤ 1 := by
    dsimp [z]
    apply (div_le_iff₀ (by linarith : 0 < 1 + δ)).mpr
    linarith
  have hp : z ^ (q - 1) ≤ z ^ i :=
    pow_le_pow_of_le_one (le_of_lt hz) hz1 (by omega)
  have he : (q : ℝ) * (1 - z) / z ≤ a * (1 - z) := by
    simpa only [div_mul_eq_mul_div] using
      mul_le_mul_of_nonneg_right ha (sub_nonneg.mpr hz1)
  have hbig : 8 ≤ z ^ i * Real.exp (a * (1 - z)) := by
    calc
      (8 : ℝ) ≤ z ^ (q - 1) * Real.exp ((q : ℝ) * (1 - z) / z) :=
        eight_le_clock_barrier hδ hδ1 q hq
      _ ≤ z ^ i * Real.exp (a * (1 - z)) := by
        exact mul_le_mul hp (Real.exp_le_exp.mpr he) (Real.exp_nonneg _)
          (pow_nonneg (le_of_lt hz) i)
  have heq : Real.exp (a * (1 - z)) = (Real.exp (a * (z - 1)))⁻¹ := by
    rw [← Real.exp_neg]
    congr 1
    ring
  rw [heq] at hbig
  apply (le_div_iff₀ (by positivity : 0 < 8 * Real.exp (a * (z - 1)))).mpr
  have h := (le_div_iff₀ (Real.exp_pos (a * (z - 1)))).mp
    (show 8 ≤ z ^ i / Real.exp (a * (z - 1)) by simpa [div_eq_mul_inv] using hbig)
  simpa using h

end RSP.Barrier
end

section
set_option autoImplicit false
namespace NearLinearRSP.TwoResources

private theorem prod_exp_resource {α : Type*} (xs : List α) (w : α → ℝ) (r z : ℝ) :
    (xs.map (fun x => Real.exp (r * w x * (z - 1)))).prod =
      Real.exp (r * (xs.map w).sum * (z - 1)) := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [List.map_cons, List.prod_cons, List.sum_cons]
    rw [ih, ← Real.exp_add]
    congr 1
    ring

private theorem lengthPGF_prod (A : InnerInput) (P : List ℕ) :
    ((P.zip P.tail).map (fun e => lengthPGF A e.1 e.2)).prod =
      Real.exp (lengthRate A * pathWeight A.I.length P * (zValue A - 1)) := by
  exact prod_exp_resource (P.zip P.tail) (fun e => (A.I.length e.1 e.2 : ℝ))
    (lengthRate A) (zValue A)

private theorem costPGF_prod (A : InnerInput) (P : List ℕ) :
    ((P.zip P.tail).map (fun e => costPGF A e.1 e.2)).prod =
      Real.exp (costRate A * pathWeight A.I.cost P * (zValue A - 1)) := by
  exact prod_exp_resource (P.zip P.tail) (fun e => (A.I.cost e.1 e.2 : ℝ))
    (costRate A) (zValue A)

private theorem zValue_pos (A : InnerInput) : 0 < zValue A := by
  unfold zValue
  have hδ := A.accuracy_pos
  positivity

private theorem normalized_resource_barrier (A : InnerInput) (B w : ℝ) (hB : 0 < B)
    (hw : (1 + A.δ) * B ≤ w) (i : ℕ) (hi : i < tickLimit A) :
    1 ≤ zValue A ^ i /
      (8 * Real.exp (((tickLimit A : ℝ) / ((1 + A.δ / 2) * B)) * w * (zValue A - 1))) := by
  have hδ := A.accuracy_pos
  have hhalf : 0 < 1 + A.δ / 2 := by linarith
  have hwhole : 0 < 1 + A.δ := by linarith
  have ha : (tickLimit A : ℝ) / zValue A ≤
      (tickLimit A : ℝ) / ((1 + A.δ / 2) * B) * w := by
    calc
      (tickLimit A : ℝ) / zValue A =
          (tickLimit A : ℝ) / ((1 + A.δ / 2) * B) * ((1 + A.δ) * B) := by
        unfold zValue
        field_simp
        <;> ring
      _ ≤ (tickLimit A : ℝ) / ((1 + A.δ / 2) * B) * w :=
        mul_le_mul_of_nonneg_left hw (by positivity)
  exact RSP.Barrier.one_le_resource_term A.accuracy_pos A.accuracy_lt_one.le
    (tickLimit A) (Nat.le_ceil _) i hi
    ((tickLimit A : ℝ) / ((1 + A.δ / 2) * B) * w) ha

private theorem potential_detects_violation_of_nonneg (A : InnerInput) (S : RetrievalState)
    (hD : 0 ≤ dpValue A (buildTable A) S.front S.i S.j) :
    (pathWeight A.I.length S.path > (1 + A.δ) * A.L → S.i < tickLimit A →
      1 ≤ potential A S) ∧
    (pathWeight A.I.cost S.path > (1 + A.δ) * A.I.budget → S.j < tickLimit A →
      1 ≤ potential A S) := by
  have hz := zValue_pos A
  unfold potential
  rw [lengthPGF_prod, costPGF_prod]
  constructor
  · intro hw hi
    have h := normalized_resource_barrier A A.L (pathWeight A.I.length S.path)
      A.length_pos hw.le S.i hi
    change 1 ≤ zValue A ^ S.i /
      (8 * Real.exp (lengthRate A * pathWeight A.I.length S.path * (zValue A - 1))) at h
    have hnonneg : 0 ≤ zValue A ^ S.j /
        (8 * Real.exp (costRate A * pathWeight A.I.cost S.path * (zValue A - 1))) := by
      positivity
    linarith
  · intro hw hj
    have h := normalized_resource_barrier A A.I.budget (pathWeight A.I.cost S.path)
      A.budget_pos hw.le S.j hj
    change 1 ≤ zValue A ^ S.j /
      (8 * Real.exp (costRate A * pathWeight A.I.cost S.path * (zValue A - 1))) at h
    have hnonneg : 0 ≤ zValue A ^ S.i /
        (8 * Real.exp (lengthRate A * pathWeight A.I.length S.path * (zValue A - 1))) := by
      positivity
    linarith

end NearLinearRSP.TwoResources
end

section
set_option autoImplicit false
namespace RSP

private theorem retrievalRank_decreases_same_layer
    (cap width spent rank rank' : ℕ) (h : rank' < rank) :
    retrievalRank cap width spent rank' < retrievalRank cap width spent rank := by
  unfold retrievalRank
  omega

private theorem retrievalRank_decreases_tick
    (cap width spent spent' rank rank' : ℕ)
    (hs : spent < spent') (hs' : spent' ≤ cap) (hr' : rank' < width) :
    retrievalRank cap width spent' rank' < retrievalRank cap width spent rank := by
  have hsub : cap - spent' + 1 ≤ cap - spent := by omega
  have hmul := Nat.mul_le_mul_right width hsub
  simp only [Nat.add_mul, Nat.one_mul] at hmul
  unfold retrievalRank
  omega

end RSP
end

section
set_option autoImplicit false
open scoped NNReal
namespace NearLinearRSP.TwoResources

private theorem retrievalStart_consistent (A : InnerInput) (t : ℕ) :
    RetrievalConsistent A (retrievalStart t) := by
  simp [RetrievalConsistent, retrievalStart]

private theorem potential_eq_stored (A : InnerInput) (S : RetrievalState)
    (hS : RetrievalConsistent A S) :
    potential A S = dpValue A (buildTable A) S.front S.i S.j + S.Hlength + S.Hcost := by
  rw [potential, hS.2.1, hS.2.2]

private theorem lengthPGF_pos (A : InnerInput) (u v : ℕ) : 0 < lengthPGF A u v :=
  Real.exp_pos _

private theorem costPGF_pos (A : InnerInput) (u v : ℕ) : 0 < costPGF A u v :=
  Real.exp_pos _

private theorem pathProduct_cons (F : ℕ → ℕ → ℝ) (P : List ℕ) (u v : ℕ)
    (hP : P.head? = some v) :
    (((u :: P).zip (u :: P).tail).map (fun e => F e.1 e.2)).prod =
      F u v * ((P.zip P.tail).map (fun e => F e.1 e.2)).prod := by
  cases P with
  | nil => simp at hP
  | cons a P =>
      have ha : a = v := by simpa using hP
      subst a
      simp

private theorem consistent_aux_pos (A : InnerInput) (S : RetrievalState)
    (hS : RetrievalConsistent A S) : 0 < S.Hlength ∧ 0 < S.Hcost := by
  rw [hS.2.1, hS.2.2, lengthPGF_prod, costPGF_prod]
  have hz := zValue_pos A
  constructor <;> positivity

private theorem crossEdge_consistent (A : InnerInput) (S : RetrievalState)
    (hS : RetrievalConsistent A S) (u a b : ℕ) :
    RetrievalConsistent A (crossEdge A S u a b) := by
  unfold RetrievalConsistent crossEdge
  simp only [List.head?_cons, true_and]
  rw [pathProduct_cons _ _ _ _ hS.1, pathProduct_cons _ _ _ _ hS.1]
  rw [hS.2.1, hS.2.2]
  constructor <;> simp only [pow_add, div_eq_mul_inv, mul_inv_rev] <;> ring

private theorem lengthTick_consistent (A : InnerInput) (S : RetrievalState)
    (hS : RetrievalConsistent A S) :
    RetrievalConsistent A { S with i := S.i + 1, Hlength := zValue A * S.Hlength } := by
  refine ⟨hS.1, ?_, hS.2.2⟩
  change zValue A * S.Hlength = zValue A ^ (S.i + 1) / _
  rw [hS.2.1, pow_succ]
  ring

private theorem costTick_consistent (A : InnerInput) (S : RetrievalState)
    (hS : RetrievalConsistent A S) :
    RetrievalConsistent A { S with j := S.j + 1, Hcost := zValue A * S.Hcost } := by
  refine ⟨hS.1, hS.2.1, ?_⟩
  change zValue A * S.Hcost = zValue A ^ (S.j + 1) / _
  rw [hS.2.2, pow_succ]
  ring

private theorem retrievalScore_eq_cross_potential (A : InnerInput) (S : RetrievalState)
    (hS : RetrievalConsistent A S) (u a b : ℕ) :
    retrievalScore A S u (a,b) = potential A (crossEdge A S u a b) := by
  rw [potential_eq_stored _ _ (crossEdge_consistent A S hS u a b)]
  rfl

private theorem mem_incrementPairs (A : InnerInput) (S : RetrievalState) (a b : ℕ) :
    (a,b) ∈ incrementPairs A S ↔ a < tickLimit A - S.i ∧ b < tickLimit A - S.j := by
  simp [incrementPairs]

private theorem incrementPairs_ne_nil (A : InnerInput) (S : RetrievalState)
    (hi : S.i < tickLimit A) (hj : S.j < tickLimit A) :
    incrementPairs A S ≠ [] := by
  have hz : (0,0) ∈ incrementPairs A S := by
    rw [mem_incrementPairs]
    omega
  intro h
  simp [h] at hz

private theorem isPath_prepend (G : Digraph) (u v t : ℕ) (P : List ℕ)
    (hP : IsPath G v t P) (he : (u,v) ∈ G.edges) : IsPath G u t (u :: P) := by
  refine ⟨rfl, ?_, ?_⟩
  · have hn : P ≠ [] := by intro h; simp [IsPath, h] at hP
    simpa [List.getLast?_cons_of_ne_nil hn] using hP.2.1
  · apply hP.2.2.cons
    intro w hw
    rw [hP.1] at hw
    have hwv : w = v := by symm; simpa using hw
    simpa [hwv] using he

end NearLinearRSP.TwoResources
end

section
set_option autoImplicit false
open scoped NNReal BigOperators
namespace NearLinearRSP.TwoResources

private theorem poissonCountMass_weighted_sum_le (r z : ℝ) (hr : 0 ≤ r) (hz : 0 ≤ z)
    (n : ℕ) :
    (∑ a ∈ Finset.range n, ActuarialValuation.poissonCountMass r a * z ^ a) ≤
      Real.exp (r * (z - 1)) := by
  exact sum_le_hasSum (Finset.range n)
    (fun a _ => mul_nonneg (RSP.PoissonBridge.poissonCountMass_nonneg r hr a)
      (pow_nonneg hz a))
    (RSP.Tails.poisson_pgf_hasSum ⟨r, hr⟩ z)

private theorem rectangle_lengthMoment_le (A : InnerInput) (u v na nb : ℕ) :
    (∑ a ∈ Finset.range na, ∑ b ∈ Finset.range nb,
      edgeMass A u v a b * zValue A ^ a) ≤ lengthPGF A u v := by
  have hl : 0 ≤ lengthRate A * A.I.length u v :=
    mul_nonneg (RSP.PoissonBridge.lengthRate_nonneg A) (A.I.length u v).coe_nonneg
  have hc : 0 ≤ costRate A * A.I.cost u v :=
    mul_nonneg (RSP.PoissonBridge.costRate_nonneg A) (A.I.cost u v).coe_nonneg
  have hlen := poissonCountMass_weighted_sum_le _ _ hl (zValue_pos A).le na
  have hcost := RSP.PoissonBridge.poissonCountMass_sum_le_one _ hc nb
  have hc0 : 0 ≤ ∑ b ∈ Finset.range nb,
      ActuarialValuation.poissonCountMass (costRate A * A.I.cost u v) b :=
    Finset.sum_nonneg (fun b _ => RSP.PoissonBridge.poissonCountMass_nonneg _ hc b)
  have hprod := mul_le_mul hlen hcost hc0 (lengthPGF_pos A u v).le
  have heq : (∑ a ∈ Finset.range na, ∑ b ∈ Finset.range nb,
      edgeMass A u v a b * zValue A ^ a) =
      (∑ a ∈ Finset.range na,
        ActuarialValuation.poissonCountMass (lengthRate A * A.I.length u v) a * zValue A ^ a) *
      (∑ b ∈ Finset.range nb,
        ActuarialValuation.poissonCountMass (costRate A * A.I.cost u v) b) := by
    rw [Finset.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    unfold edgeMass
    ring
  rw [heq]
  simpa [lengthPGF] using hprod

private theorem rectangle_costMoment_le (A : InnerInput) (u v na nb : ℕ) :
    (∑ a ∈ Finset.range na, ∑ b ∈ Finset.range nb,
      edgeMass A u v a b * zValue A ^ b) ≤ costPGF A u v := by
  have hl : 0 ≤ lengthRate A * A.I.length u v :=
    mul_nonneg (RSP.PoissonBridge.lengthRate_nonneg A) (A.I.length u v).coe_nonneg
  have hc : 0 ≤ costRate A * A.I.cost u v :=
    mul_nonneg (RSP.PoissonBridge.costRate_nonneg A) (A.I.cost u v).coe_nonneg
  have hlen := RSP.PoissonBridge.poissonCountMass_sum_le_one _ hl na
  have hcost := poissonCountMass_weighted_sum_le _ _ hc (zValue_pos A).le nb
  have hc0 : 0 ≤ ∑ b ∈ Finset.range nb,
      ActuarialValuation.poissonCountMass (costRate A * A.I.cost u v) b * zValue A ^ b :=
    Finset.sum_nonneg (fun b _ => mul_nonneg
      (RSP.PoissonBridge.poissonCountMass_nonneg _ hc b) (pow_nonneg (zValue_pos A).le b))
  have hprod := mul_le_mul hlen hcost hc0 zero_le_one
  have heq : (∑ a ∈ Finset.range na, ∑ b ∈ Finset.range nb,
      edgeMass A u v a b * zValue A ^ b) =
      (∑ a ∈ Finset.range na,
        ActuarialValuation.poissonCountMass (lengthRate A * A.I.length u v) a) *
      (∑ b ∈ Finset.range nb,
        ActuarialValuation.poissonCountMass (costRate A * A.I.cost u v) b * zValue A ^ b) := by
    rw [Finset.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    unfold edgeMass
    ring
  rw [heq]
  simpa [costPGF] using hprod

private theorem exists_below_of_weighted_lt {α : Type*} (s : Finset α) (p f : α → ℝ)
    (hp : ∀ a ∈ s, 0 ≤ p a)
    (h : ∑ a ∈ s, p a * f a < ∑ a ∈ s, p a) :
    ∃ a ∈ s, f a < 1 := by
  by_contra hn
  push Not at hn
  have hge : (∑ a ∈ s, p a) ≤ ∑ a ∈ s, p a * f a := by
    apply Finset.sum_le_sum
    intro a ha
    simpa using mul_le_mul_of_nonneg_left (hn a ha) (hp a ha)
  linarith

private theorem potential_lt_one_unsaturated (A : InnerInput) (S : RetrievalState)
    (hS : RetrievalConsistent A S) (hΦ : potential A S < 1) :
    S.i < tickLimit A ∧ S.j < tickLimit A := by
  have hH := consistent_aux_pos A S hS
  rw [potential_eq_stored A S hS] at hΦ
  by_contra h
  push Not at h
  have hs : tickLimit A ≤ S.i ∨ tickLimit A ≤ S.j := by omega
  have hd : dpValue A (buildTable A) S.front S.i S.j = 1 := by simp [dpValue, hs]
  rw [hd] at hΦ
  linarith

private theorem edge_has_score_below_one_of_bellman (A : InnerInput) (S : RetrievalState)
    (u : ℕ) (hS : RetrievalConsistent A S) (hΦ : potential A S < 1)
    (hBellman : dpValue A (buildTable A) S.front S.i S.j =
      edgeExpectation A (buildTable A) u S.front S.i S.j) :
    ∃ ab ∈ incrementPairs A S, retrievalScore A S u ab < 1 := by
  have hs := potential_lt_one_unsaturated A S hS hΦ
  have hH := consistent_aux_pos A S hS
  have hl := rectangle_lengthMoment_le A u S.front (tickLimit A - S.i) (tickLimit A - S.j)
  have hc := rectangle_costMoment_le A u S.front (tickLimit A - S.i) (tickLimit A - S.j)
  have hl' := mul_le_mul_of_nonneg_right hl (div_nonneg hH.1.le (lengthPGF_pos A u S.front).le)
  have hc' := mul_le_mul_of_nonneg_right hc (div_nonneg hH.2.le (costPGF_pos A u S.front).le)
  have hlbound : (∑ a ∈ Finset.range (tickLimit A - S.i),
      ∑ b ∈ Finset.range (tickLimit A - S.j),
        edgeMass A u S.front a b * (zValue A ^ a * S.Hlength / lengthPGF A u S.front)) ≤
        S.Hlength := by
    calc
      _ = (∑ a ∈ Finset.range (tickLimit A - S.i),
        ∑ b ∈ Finset.range (tickLimit A - S.j), edgeMass A u S.front a b * zValue A ^ a) *
          (S.Hlength / lengthPGF A u S.front) := by
            simp only [Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro a _
            apply Finset.sum_congr rfl
            intro b _
            ring
      _ ≤ lengthPGF A u S.front * (S.Hlength / lengthPGF A u S.front) := hl'
      _ = S.Hlength := by field_simp [ne_of_gt (lengthPGF_pos A u S.front)]
  have hcbound : (∑ a ∈ Finset.range (tickLimit A - S.i),
      ∑ b ∈ Finset.range (tickLimit A - S.j),
        edgeMass A u S.front a b * (zValue A ^ b * S.Hcost / costPGF A u S.front)) ≤
        S.Hcost := by
    calc
      _ = (∑ a ∈ Finset.range (tickLimit A - S.i),
        ∑ b ∈ Finset.range (tickLimit A - S.j), edgeMass A u S.front a b * zValue A ^ b) *
          (S.Hcost / costPGF A u S.front) := by
            simp only [Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro a _
            apply Finset.sum_congr rfl
            intro b _
            ring
      _ ≤ costPGF A u S.front * (S.Hcost / costPGF A u S.front) := hc'
      _ = S.Hcost := by field_simp [ne_of_gt (costPGF_pos A u S.front)]
  have hn : ¬ (tickLimit A ≤ S.i ∨ tickLimit A ≤ S.j) := by omega
  rw [edgeExpectation, if_neg hn] at hBellman
  rw [potential_eq_stored A S hS] at hΦ
  have hscore : (∑ a ∈ Finset.range (tickLimit A - S.i),
      ∑ b ∈ Finset.range (tickLimit A - S.j),
        edgeMass A u S.front a b * retrievalScore A S u (a,b)) <
      ∑ a ∈ Finset.range (tickLimit A - S.i),
        ∑ b ∈ Finset.range (tickLimit A - S.j), edgeMass A u S.front a b := by
    simp only [retrievalScore, mul_add, Finset.sum_add_distrib]
    linarith
  obtain ⟨⟨a,b⟩, hab, hsmall⟩ := exists_below_of_weighted_lt
    ((Finset.range (tickLimit A - S.i)) ×ˢ (Finset.range (tickLimit A - S.j)))
    (fun ab => edgeMass A u S.front ab.1 ab.2) (retrievalScore A S u)
    (fun ab _ => RSP.PoissonBridge.edgeMass_nonneg A u S.front ab.1 ab.2)
    (by simpa [Finset.sum_product] using hscore)
  refine ⟨(a,b), ?_, hsmall⟩
  simpa [mem_incrementPairs] using hab

end NearLinearRSP.TwoResources
end

section
set_option autoImplicit false
namespace NearLinearRSP.TwoResources

private theorem zValue_le_one (A : InnerInput) : zValue A ≤ 1 := by
  have hp : 0 < 1 + A.δ := by linarith [A.accuracy_pos]
  unfold zValue
  apply (div_le_iff₀ hp).mpr
  linarith [A.accuracy_pos]

private theorem retrievalStart_potential_lt_one (A : InnerInput) (t : ℕ)
    (h : accepted A t) : potential A (retrievalStart t) < 1 := by
  have hc := retrievalStart_consistent A t
  rw [potential_eq_stored _ _ hc]
  change dpValue A (buildTable A) t 0 0 + 1 / 8 + 1 / 8 < 1
  change dpValue A (buildTable A) t 0 0 ≤ 1 / 4 at h
  linarith

private theorem lengthTick_potential_le (A : InnerInput) (S : RetrievalState)
    (hS : RetrievalConsistent A S)
    (hEq : dpValue A (buildTable A) S.front S.i S.j =
      dpValue A (buildTable A) S.front (S.i + 1) S.j) :
    potential A { S with i := S.i + 1, Hlength := zValue A * S.Hlength } ≤ potential A S := by
  rw [potential_eq_stored _ _ (lengthTick_consistent A S hS),
    potential_eq_stored _ _ hS]
  change dpValue A (buildTable A) S.front (S.i + 1) S.j +
    zValue A * S.Hlength + S.Hcost ≤
      dpValue A (buildTable A) S.front S.i S.j + S.Hlength + S.Hcost
  rw [hEq]
  have hmul := mul_le_mul_of_nonneg_right (zValue_le_one A) (consistent_aux_pos A S hS).1.le
  linarith

private theorem costTick_potential_le (A : InnerInput) (S : RetrievalState)
    (hS : RetrievalConsistent A S)
    (hEq : dpValue A (buildTable A) S.front S.i S.j =
      dpValue A (buildTable A) S.front S.i (S.j + 1)) :
    potential A { S with j := S.j + 1, Hcost := zValue A * S.Hcost } ≤ potential A S := by
  rw [potential_eq_stored _ _ (costTick_consistent A S hS),
    potential_eq_stored _ _ hS]
  change dpValue A (buildTable A) S.front S.i (S.j + 1) +
    S.Hlength + zValue A * S.Hcost ≤
      dpValue A (buildTable A) S.front S.i S.j + S.Hlength + S.Hcost
  rw [hEq]
  have hmul := mul_le_mul_of_nonneg_right (zValue_le_one A) (consistent_aux_pos A S hS).2.le
  linarith

private theorem edge_retrievalStep_good (A : InnerInput) (S : RetrievalState) (u : ℕ)
    (hS : RetrievalConsistent A S) (hΦ : potential A S < 1)
    (hp : (buildTable A S.front S.i S.j).parent = .edge u)
    (hEq : dpValue A (buildTable A) S.front S.i S.j =
      edgeExpectation A (buildTable A) u S.front S.i S.j) :
    ∃ U, retrievalStep A S = some U ∧ RetrievalConsistent A U ∧ potential A U < 1 := by
  have hs := potential_lt_one_unsaturated A S hS hΦ
  have hn : ¬ (tickLimit A ≤ S.i ∨ tickLimit A ≤ S.j) := by omega
  have hne := incrementPairs_ne_nil A S hs.1 hs.2
  obtain ⟨y, hy, hscore⟩ := edge_has_score_below_one_of_bellman A S u hS hΦ hEq
  cases hlist : incrementPairs A S with
  | nil => contradiction
  | cons p ps =>
      let ab := firstMin (retrievalScore A S u) (incrementPairs A S) p
      have hmin : retrievalScore A S u ab < 1 :=
        (firstMin_le_of_mem _ _ p y hy).trans_lt hscore
      refine ⟨crossEdge A S u ab.1 ab.2, ?_, crossEdge_consistent A S hS u ab.1 ab.2, ?_⟩
      · simp [retrievalStep, hn, hp, hlist, ab]
      · rw [← retrievalScore_eq_cross_potential A S hS]
        exact hmin

private theorem retrievalStep_good_of_parent_rules (A : InnerInput) (S : RetrievalState)
    (hS : RetrievalConsistent A S) (hΦ : potential A S < 1)
    (hnone : (buildTable A S.front S.i S.j).parent ≠ .none)
    (hl : (buildTable A S.front S.i S.j).parent = .lengthTick →
      dpValue A (buildTable A) S.front S.i S.j =
      dpValue A (buildTable A) S.front (S.i + 1) S.j)
    (hc : (buildTable A S.front S.i S.j).parent = .costTick →
      dpValue A (buildTable A) S.front S.i S.j =
      dpValue A (buildTable A) S.front S.i (S.j + 1))
    (he : ∀ u, (buildTable A S.front S.i S.j).parent = .edge u →
      dpValue A (buildTable A) S.front S.i S.j =
      edgeExpectation A (buildTable A) u S.front S.i S.j) :
    ∃ U, retrievalStep A S = some U ∧ RetrievalConsistent A U ∧ potential A U < 1 := by
  have hs := potential_lt_one_unsaturated A S hS hΦ
  have hn : ¬ (tickLimit A ≤ S.i ∨ tickLimit A ≤ S.j) := by omega
  cases hp : (buildTable A S.front S.i S.j).parent with
  | none => exact False.elim (hnone hp)
  | lengthTick =>
      refine ⟨{ S with i := S.i + 1, Hlength := zValue A * S.Hlength }, ?_,
        lengthTick_consistent A S hS, ?_⟩
      · simp [retrievalStep, hn, hp]
      · exact (lengthTick_potential_le A S hS (hl hp)).trans_lt hΦ
  | costTick =>
      refine ⟨{ S with j := S.j + 1, Hcost := zValue A * S.Hcost }, ?_,
        costTick_consistent A S hS, ?_⟩
      · simp [retrievalStep, hn, hp]
      · exact (costTick_potential_le A S hS (hc hp)).trans_lt hΦ
  | edge u => exact edge_retrievalStep_good A S u hS hΦ hp (he u hp)

private theorem retrievalStep_path (A : InnerInput) (t : ℕ) (S U : RetrievalState)
    (hP : IsPath A.I.graph S.front t S.path)
    (he : ∀ u, (buildTable A S.front S.i S.j).parent = .edge u →
      (u,S.front) ∈ A.I.graph.edges)
    (hstep : retrievalStep A S = some U) : IsPath A.I.graph U.front t U.path := by
  unfold retrievalStep at hstep
  split at hstep
  · contradiction
  · split at hstep
    · contradiction
    · cases hstep; exact hP
    · cases hstep; exact hP
    · rename_i u hp
      split at hstep
      · contradiction
      · cases hstep
        exact isPath_prepend A.I.graph u S.front t S.path hP (he u hp)

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

private theorem buildTable_parent_none_only_source (A : InnerInput) (v i j : ℕ)
    (hp : (buildTable A v i j).parent = .none) : v = A.I.source := by
  have h := buildTable_parentsSupported A v i j
  simpa [hp, ParentSupported] using h

private theorem buildTable_parent_ne_none (A : InnerInput) (v i j : ℕ) (hv : v ≠ A.I.source) :
    (buildTable A v i j).parent ≠ .none := by
  intro hp
  exact hv (buildTable_parent_none_only_source A v i j hp)

private theorem buildTable_parent_edge_mem (A : InnerInput) (v i j u : ℕ)
    (hp : (buildTable A v i j).parent = .edge u) : (u,v) ∈ A.I.graph.edges := by
  have h := buildTable_parentsSupported A v i j
  simpa [hp, ParentSupported] using h

private theorem retrievalRun_success_of_rank (A : InnerInput)
    (Good : RetrievalState → Prop) (rank : RetrievalState → ℕ)
    (hstep : ∀ S, Good S → ¬ RetrievalTerminal A S →
      ∃ U, retrievalStep A S = some U ∧ Good U ∧ rank U < rank S)
    (fuel : ℕ) (S : RetrievalState) (hS : Good S) (hrank : rank S ≤ fuel) :
    ∃ U, retrievalRun A fuel S = some U ∧ Good U ∧ RetrievalTerminal A U := by
  induction fuel generalizing S with
  | zero =>
      have ht : RetrievalTerminal A S := by
        by_contra hn
        obtain ⟨U, _, _, hlt⟩ := hstep S hS hn
        omega
      change S.front = A.I.source ∧ S.i < tickLimit A ∧ S.j < tickLimit A at ht
      exact ⟨S, by simp only [retrievalRun, if_pos ht], hS, ht⟩
  | succ fuel ih =>
      by_cases ht : RetrievalTerminal A S
      · change S.front = A.I.source ∧ S.i < tickLimit A ∧ S.j < tickLimit A at ht
        exact ⟨S, by simp only [retrievalRun, if_pos ht], hS, ht⟩
      · obtain ⟨T, hst, hT, hdec⟩ := hstep S hS ht
        change ¬ (S.front = A.I.source ∧ S.i < tickLimit A ∧ S.j < tickLimit A) at ht
        obtain ⟨U, hrun, hU, hterm⟩ := ih T hT (by omega)
        refine ⟨U, ?_, hU, hterm⟩
        simpa [retrievalRun, RetrievalTerminal, ht, hst] using hrun

private theorem actualRetrievalRank_initial_le_fuel (A : InnerInput) (t : ℕ)
    (hr : (buildTable A t 0 0).rank ≤ (activeVertices A.I).length) :
    actualRetrievalRank A (retrievalStart t) ≤ retrievalFuel A := by
  unfold actualRetrievalRank RSP.retrievalRank retrievalStart retrievalFuel
  simp only [Nat.zero_add, Nat.sub_zero]
  have : (buildTable A t 0 0).rank ≤ (activeVertices A.I).length + 1 := by omega
  nlinarith

private theorem actualRetrievalRank_decreases (A : InnerInput) (S U : RetrievalState)
    (hi : U.i < tickLimit A) (hj : U.j < tickLimit A)
    (hbound : (buildTable A U.front U.i U.j).rank ≤ (activeVertices A.I).length)
    (hprogress : S.i + S.j < U.i + U.j ∨
      (S.i + S.j = U.i + U.j ∧
        (buildTable A U.front U.i U.j).rank < (buildTable A S.front S.i S.j).rank)) :
    actualRetrievalRank A U < actualRetrievalRank A S := by
  unfold actualRetrievalRank
  rcases hprogress with h | ⟨heq, h⟩
  · exact RSP.retrievalRank_decreases_tick _ _ _ _ _ _ h (by omega) (by omega)
  · rw [← heq]
    exact RSP.retrievalRank_decreases_same_layer _ _ _ _ _ h

private theorem retrievalStep_progress (A : InnerInput) (S U : RetrievalState)
    (hr : ∀ u, (buildTable A S.front S.i S.j).parent = .edge u →
      (buildTable A u S.i S.j).rank < (buildTable A S.front S.i S.j).rank)
    (hstep : retrievalStep A S = some U) :
    S.i + S.j < U.i + U.j ∨
      (S.i + S.j = U.i + U.j ∧
        (buildTable A U.front U.i U.j).rank < (buildTable A S.front S.i S.j).rank) := by
  unfold retrievalStep at hstep
  split at hstep
  · contradiction
  · split at hstep
    · contradiction
    · cases hstep
      left
      change S.i + S.j < (S.i + 1) + S.j
      omega
    · cases hstep
      left
      change S.i + S.j < S.i + (S.j + 1)
      omega
    · rename_i u hp
      split at hstep
      · contradiction
      · rename_i p ps hlist
        cases hstep
        simp only [crossEdge]
        by_cases hzero :
            (firstMin (retrievalScore A S u) (incrementPairs A S) p).1 +
            (firstMin (retrievalScore A S u) (incrementPairs A S) p).2 = 0
        · have ha : (firstMin (retrievalScore A S u) (incrementPairs A S) p).1 = 0 := by omega
          have hb : (firstMin (retrievalScore A S u) (incrementPairs A S) p).2 = 0 := by omega
          right
          simpa [ha, hb] using hr u hp
        · left
          omega

private theorem deterministic_retrieval_of_table_facts (A : InnerInput) (t : ℕ)
    (haccept : accepted A t)
    (hnone : ∀ v i j, v ≠ A.I.source →
      (buildTable A v i j).parent ≠ .none)
    (hlength : ∀ v i j, (buildTable A v i j).parent = .lengthTick →
      dpValue A (buildTable A) v i j = dpValue A (buildTable A) v (i+1) j)
    (hcost : ∀ v i j, (buildTable A v i j).parent = .costTick →
      dpValue A (buildTable A) v i j = dpValue A (buildTable A) v i (j+1))
    (hedge : ∀ v i j u, (buildTable A v i j).parent = .edge u →
      dpValue A (buildTable A) v i j = edgeExpectation A (buildTable A) u v i j)
    (hgraph : ∀ v i j u, (buildTable A v i j).parent = .edge u →
      (u,v) ∈ A.I.graph.edges)
    (hrank : ∀ v i j, (buildTable A v i j).rank ≤ (activeVertices A.I).length)
    (hparentRank : ∀ v i j u, (buildTable A v i j).parent = .edge u →
      (buildTable A u i j).rank < (buildTable A v i j).rank) :
    ∃ U : RetrievalState, retrieve A t = some U ∧
      IsPath A.I.graph A.I.source t U.path ∧
      pathWeight A.I.length U.path ≤ (1 + A.δ) * A.L ∧
      pathWeight A.I.cost U.path ≤ (1 + A.δ) * A.I.budget := by
  let Good : RetrievalState → Prop := fun S =>
    RetrievalConsistent A S ∧ IsPath A.I.graph S.front t S.path ∧ potential A S < 1
  have hstep : ∀ S, Good S → ¬ RetrievalTerminal A S →
      ∃ U, retrievalStep A S = some U ∧ Good U ∧
        actualRetrievalRank A U < actualRetrievalRank A S := by
    intro S hS hnterm
    have hs := potential_lt_one_unsaturated A S hS.1 hS.2.2
    have hv : S.front ≠ A.I.source := by
      intro hv
      exact hnterm ⟨hv, hs⟩
    obtain ⟨U, hst, hU, hΦ⟩ := retrievalStep_good_of_parent_rules A S hS.1 hS.2.2
      (hnone S.front S.i S.j hv) (hlength S.front S.i S.j) (hcost S.front S.i S.j)
      (hedge S.front S.i S.j)
    have hu := potential_lt_one_unsaturated A U hU hΦ
    refine ⟨U, hst, ⟨hU,
      retrievalStep_path A t S U hS.2.1 (hgraph S.front S.i S.j) hst, hΦ⟩, ?_⟩
    exact actualRetrievalRank_decreases A S U hu.1 hu.2 (hrank U.front U.i U.j)
      (retrievalStep_progress A S U (hparentRank S.front S.i S.j) hst)
  have hstart : Good (retrievalStart t) := by
    refine ⟨retrievalStart_consistent A t, ?_, retrievalStart_potential_lt_one A t haccept⟩
    simp [retrievalStart, IsPath]
  obtain ⟨U, hrun, hU, hterm⟩ := retrievalRun_success_of_rank A Good
    (actualRetrievalRank A) hstep (retrievalFuel A) (retrievalStart t) hstart
    (actualRetrievalRank_initial_le_fuel A t (hrank t 0 0))
  refine ⟨U, hrun, ?_, ?_, ?_⟩
  · simpa [hterm.1] using hU.2.1
  · by_contra hbad
    have hdet := (potential_detects_violation_of_nonneg A U
      (dpValue_buildTable_nonneg A U.front U.i U.j)).1 (lt_of_not_ge hbad) hterm.2.1
    exact (not_le_of_gt hU.2.2) hdet
  · by_contra hbad
    have hdet := (potential_detects_violation_of_nonneg A U
      (dpValue_buildTable_nonneg A U.front U.i U.j)).2 (lt_of_not_ge hbad) hterm.2.2
    exact (not_le_of_gt hU.2.2) hdet

private theorem edgeExpectation_putCell_other (A : InnerInput) (T : Table)
    (w u v i j : ℕ) (c : Cell) (hu : u ≠ w) :
    edgeExpectation A (putCell T w i j c) u v i j = edgeExpectation A T u v i j := by
  simp [edgeExpectation, dpValue, putCell, hu]

private theorem dpValue_putCell_next_length (A : InnerInput) (T : Table)
    (u v i j : ℕ) (c : Cell) :
    dpValue A (putCell T u i j c) v (i + 1) j = dpValue A T v (i + 1) j := by
  simp [dpValue, putCell]

private theorem dpValue_putCell_next_cost (A : InnerInput) (T : Table)
    (u v i j : ℕ) (c : Cell) :
    dpValue A (putCell T u i j c) v i (j + 1) = dpValue A T v i (j + 1) := by
  simp [dpValue, putCell]

private theorem initLayer_tickConsistency (A : InnerInput) (T : Table) (i j : ℕ) :
    TickConsistency A i j (initLayer A T i j) := by
  intro v
  by_cases hv : v = A.I.source
  · simp [initLayer, hv]
  · by_cases hle : dpValue A T v (i + 1) j ≤ dpValue A T v i (j + 1)
    · simp [initLayer, hv, hle, min_eq_left hle]
    · simp [initLayer, hv, hle, min_eq_right (le_of_not_ge hle)]

private theorem initLayer_edgeConsistency (A : InnerInput) (T : Table) (i j : ℕ) :
    EdgeConsistency A i j (initLayer A T i j) := by
  intro v u hp
  simp only [initLayer] at hp
  split_ifs at hp <;> contradiction

private theorem relaxEdge_tickConsistency (A : InnerInput) (i j u : ℕ) (S : LayerState)
    (e : ℕ × ℕ) (h : TickConsistency A i j S) :
    TickConsistency A i j (relaxEdge A i j u S e) := by
  unfold relaxEdge
  dsimp only
  split
  · split
    · intro v
      by_cases hv : v = e.2
      · subst v
        simp
      · simpa [Function.update_of_ne hv] using h v
    · exact h
  · exact h

private theorem relaxAll_tickConsistency (A : InnerInput) (i j u : ℕ) (S : LayerState)
    (h : TickConsistency A i j S) : TickConsistency A i j (relaxAll A i j u S) := by
  unfold relaxAll
  generalize A.I.graph.edges = es
  induction es generalizing S with
  | nil => exact h
  | cons e es ih =>
      rw [List.foldl_cons]
      exact ih _ (relaxEdge_tickConsistency A i j u S e h)

private theorem settleState_tickConsistency (A : InnerInput) (i j u : ℕ) (S : LayerState)
    (h : TickConsistency A i j S) : TickConsistency A i j (settleState S i j u) := by
  intro v
  change (S.parents v = .lengthTick → S.keys v = dpValue A (putCell S.table u i j _) v (i + 1) j) ∧
    (S.parents v = .costTick → S.keys v = dpValue A (putCell S.table u i j _) v i (j + 1))
  rw [dpValue_putCell_next_length, dpValue_putCell_next_cost]
  exact h v

private theorem popLayer_tickConsistency (A : InnerInput) (i j : ℕ) (S : LayerState)
    (h : TickConsistency A i j S) : TickConsistency A i j (popLayer A i j S) := by
  unfold popLayer
  split
  · exact h
  · change TickConsistency A i j (relaxAll A i j _ (settleState S i j _))
    exact relaxAll_tickConsistency A i j _ _ (settleState_tickConsistency A i j _ S h)

private theorem queueRun_tickConsistency (A : InnerInput) (i j n : ℕ) (S : LayerState)
    (h : TickConsistency A i j S) : TickConsistency A i j (queueRun A i j n S) := by
  induction n with
  | zero => exact h
  | succ n ih => rw [queueRun_succ]; exact popLayer_tickConsistency A i j _ ih

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

private theorem buildLayer_selected_ticks (A : InnerInput) (T : Table) (i j v : ℕ)
    (hv : v ∈ activeVertices A.I) :
    ((buildLayer A T i j v i j).parent = .lengthTick →
      (buildLayer A T i j v i j).value = dpValue A (buildLayer A T i j) v (i + 1) j) ∧
    ((buildLayer A T i j v i j).parent = .costTick →
      (buildLayer A T i j v i j).value = dpValue A (buildLayer A T i j) v i (j + 1)) := by
  let S := initLayer A T i j
  let n := (activeVertices A.I).length
  have hs : PoppedSync A i j S := by intro v hv hn; exact False.elim (hn hv)
  have hp' : PoppedParentSync A i j S := by intro v hv hn; exact False.elim (hn hv)
  have hsync := queueRun_sync A i j n S (activeVertices_nodup A.I) hs
  have hpsync := queueRun_parentSync A i j n S hp'
  have ht := queueRun_tickConsistency A i j n S (initLayer_tickConsistency A T i j)
  have hnot : v ∉ (queueRun A i j n S).queue := by
    rw [buildLayer_queue_exhausted A T i j]; simp
  constructor
  · intro hp
    exact (hsync v hv hnot).trans ((ht v).1 ((hpsync v hv hnot).symm.trans hp))
  · intro hp
    exact (hsync v hv hnot).trans ((ht v).2 ((hpsync v hv hnot).symm.trans hp))

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

private theorem initLayer_ranks (A : InnerInput) (T : Table) (i j : ℕ) :
    LayerRanks A i j (initLayer A T i j) := by
  constructor
  · intro v hv hn
    exact False.elim (hn hv)
  · intro v u hp
    simp only [initLayer] at hp
    split_ifs at hp
  · intro v hv hn
    exact False.elim (hn hv)

private theorem settleState_ranks (A : InnerInput) (i j u : ℕ) (S : LayerState)
    (hu : u ∈ S.queue) (h : LayerRanks A i j S) :
    LayerRanks A i j (settleState S i j u) := by
  constructor
  · intro v hv hn
    change (putCell S.table u i j _ v i j).rank < S.nextRank + 1
    by_cases hvu : v = u
    · subst v
      simp
    · rw [putCell_other_vertex _ _ _ _ _ _ hvu]
      have hn' : v ∉ S.queue := fun hm => hn ((List.mem_erase_of_ne hvu).mpr hm)
      exact (h.settled v hv hn').trans (Nat.lt_succ_self _)
  · intro v p hp
    have hold := h.pending v p hp
    have hpu : p ≠ u := by intro heq; subst p; exact hold.1 hu
    refine ⟨fun hm => hold.1 (List.mem_of_mem_erase hm), ?_⟩
    change (putCell S.table u i j _ p i j).rank < S.nextRank + 1
    rw [putCell_other_vertex _ _ _ _ _ _ hpu]
    exact hold.2.trans (Nat.lt_succ_self _)
  · intro v hv hn p hp
    by_cases hvu : v = u
    · subst v
      have hparent : S.parents u = .edge p := by simpa [settleState] using hp
      have hold := h.pending u p hparent
      have hpu : p ≠ u := by intro heq; subst p; exact hold.1 hu
      refine ⟨fun hm => hold.1 (List.mem_of_mem_erase hm), ?_⟩
      change (putCell S.table u i j _ p i j).rank < (putCell S.table u i j _ u i j).rank
      rw [putCell_other_vertex _ _ _ _ _ _ hpu, putCell_same]
      exact hold.2
    · have hn' : v ∉ S.queue := fun hm => hn ((List.mem_erase_of_ne hvu).mpr hm)
      have hp' : (S.table v i j).parent = .edge p := by
        simpa [settleState, putCell_other_vertex _ _ _ _ _ _ hvu] using hp
      have hold := h.edge v hv hn' p hp'
      have hpu : p ≠ u := by intro heq; subst p; exact hold.1 hu
      refine ⟨fun hm => hold.1 (List.mem_of_mem_erase hm), ?_⟩
      change (putCell S.table u i j _ p i j).rank < (putCell S.table u i j _ v i j).rank
      rw [putCell_other_vertex _ _ _ _ _ _ hpu, putCell_other_vertex _ _ _ _ _ _ hvu]
      exact hold.2

private theorem relaxEdge_ranks (A : InnerInput) (i j u : ℕ) (S : LayerState)
    (e : ℕ × ℕ) (hu : u ∉ S.queue) (hur : (S.table u i j).rank < S.nextRank)
    (h : LayerRanks A i j S) : LayerRanks A i j (relaxEdge A i j u S e) := by
  unfold relaxEdge
  dsimp only
  split
  · split
    · constructor
      · exact h.settled
      · intro v p hp
        by_cases hv : v = e.2
        · subst v
          simp only [Function.update_self, Parent.edge.injEq] at hp
          subst p
          exact ⟨hu, hur⟩
        · simp only [Function.update_of_ne hv] at hp
          exact h.pending v p hp
      · exact h.edge
    · exact h
  · exact h

private theorem relaxAll_ranks (A : InnerInput) (i j u : ℕ) (S : LayerState)
    (hu : u ∉ S.queue) (hur : (S.table u i j).rank < S.nextRank)
    (h : LayerRanks A i j S) : LayerRanks A i j (relaxAll A i j u S) := by
  unfold relaxAll
  generalize A.I.graph.edges = es
  induction es generalizing S with
  | nil => exact h
  | cons e es ih =>
      rw [List.foldl_cons]
      exact ih _ (by simpa using hu) (by simpa using hur)
        (relaxEdge_ranks A i j u S e hu hur h)

private theorem popLayer_ranks (A : InnerInput) (i j : ℕ) (S : LayerState)
    (hdup : S.queue.Nodup) (h : LayerRanks A i j S) :
    LayerRanks A i j (popLayer A i j S) := by
  by_cases hne : S.queue = []
  · simpa [popLayer, hne] using h
  · rw [popLayer_eq_relaxAll A i j S hne]
    apply relaxAll_ranks
    · exact hdup.not_mem_erase
    · simp [settleState]
    · exact settleState_ranks A i j _ S (pickedVertex_mem S hne) h

private theorem queueRun_ranks (A : InnerInput) (i j n : ℕ) (S : LayerState)
    (hdup : S.queue.Nodup) (h : LayerRanks A i j S) :
    LayerRanks A i j (queueRun A i j n S) := by
  induction n with
  | zero => exact h
  | succ n ih =>
      rw [queueRun_succ]
      exact popLayer_ranks A i j _ (queueRun_queue_nodup A i j n S hdup) ih

private theorem buildLayer_parent_rank (A : InnerInput) (T : Table) (i j v u : ℕ)
    (hv : v ∈ activeVertices A.I)
    (hp : (buildLayer A T i j v i j).parent = .edge u) :
    (buildLayer A T i j u i j).rank < (buildLayer A T i j v i j).rank := by
  have h := queueRun_ranks A i j (activeVertices A.I).length (initLayer A T i j)
    (activeVertices_nodup A.I) (initLayer_ranks A T i j)
  have hn : v ∉ (queueRun A i j (activeVertices A.I).length (initLayer A T i j)).queue := by
    rw [buildLayer_queue_exhausted]
    simp
  exact (h.edge v hv hn u hp).2

private theorem initLayer_rankBound (A : InnerInput) (T : Table) (i j : ℕ)
    (hT : TableRankBound T (activeVertices A.I).length) :
    LayerRankBound (initLayer A T i j) (activeVertices A.I).length := by
  exact ⟨hT, by simp [initLayer]⟩

private theorem relaxAll_rankBound (A : InnerInput) (i j u : ℕ) (S : LayerState) (n : ℕ)
    (h : LayerRankBound S n) : LayerRankBound (relaxAll A i j u S) n := by
  simpa only [LayerRankBound, relaxAll_table, relaxAll_nextRank, relaxAll_queue] using h

private theorem settleState_rankBound (i j u : ℕ) (S : LayerState) (n : ℕ)
    (hu : u ∈ S.queue) (h : LayerRankBound S n) :
    LayerRankBound (settleState S i j u) n := by
  constructor
  · intro v a b
    change (putCell S.table u i j _ v a b).rank ≤ n
    unfold putCell
    split
    · have hc := h.2
      dsimp only
      omega
    · exact h.1 v a b
  · change S.nextRank + 1 + (S.queue.erase u).length = n
    rw [List.length_erase_of_mem hu]
    have hc := h.2
    have hlen : 0 < S.queue.length := List.length_pos_iff.mpr (List.ne_nil_of_mem hu)
    omega

private theorem popLayer_rankBound (A : InnerInput) (i j : ℕ) (S : LayerState) (n : ℕ)
    (h : LayerRankBound S n) : LayerRankBound (popLayer A i j S) n := by
  by_cases hne : S.queue = []
  · simpa [popLayer, hne] using h
  · rw [popLayer_eq_relaxAll A i j S hne]
    exact relaxAll_rankBound A i j _ _ n
      (settleState_rankBound i j _ S n (pickedVertex_mem S hne) h)

private theorem queueRun_rankBound (A : InnerInput) (i j k : ℕ) (S : LayerState) (n : ℕ)
    (h : LayerRankBound S n) : LayerRankBound (queueRun A i j k S) n := by
  induction k with
  | zero => exact h
  | succ k ih => rw [queueRun_succ]; exact popLayer_rankBound A i j _ n ih

private theorem buildLayer_rankBound (A : InnerInput) (T : Table) (i j : ℕ)
    (hT : TableRankBound T (activeVertices A.I).length) :
    TableRankBound (buildLayer A T i j) (activeVertices A.I).length :=
  (queueRun_rankBound A i j _ _ _ (initLayer_rankBound A T i j hT)).1

private theorem runLayers_rankBound (A : InnerInput) (layers : List (ℕ × ℕ)) (T : Table)
    (hT : TableRankBound T (activeVertices A.I).length) :
    TableRankBound (runLayers A layers T) (activeVertices A.I).length := by
  induction layers generalizing T with
  | nil => exact hT
  | cons p ps ih => exact ih _ (buildLayer_rankBound A T p.1 p.2 hT)

private theorem buildTable_rank_le (A : InnerInput) (v i j : ℕ) :
    (buildTable A v i j).rank ≤ (activeVertices A.I).length := by
  rw [buildTable_eq_runLayers]
  exact runLayers_rankBound A _ _ (by intro v a b; exact Nat.zero_le _) v i j

private theorem buildTable_outside (A : InnerInput) (v i j : ℕ)
    (hsat : tickLimit A ≤ i ∨ tickLimit A ≤ j) :
    buildTable A v i j = ⟨1, .lengthTick, 0⟩ := by
  rw [buildTable_eq_runLayers]
  apply runLayers_frame
  intro p hp
  have hp' := (layerSchedule_mem A p.1 p.2).mp hp
  omega

private theorem buildTable_outside_parent (A : InnerInput) (v i j : ℕ)
    (hsat : tickLimit A ≤ i ∨ tickLimit A ≤ j) :
    (buildTable A v i j).parent = .lengthTick := by
  rw [buildTable_outside A v i j hsat]

private theorem buildTable_edge_parent_nonsaturated (A : InnerInput) (v i j u : ℕ)
    (hp : (buildTable A v i j).parent = .edge u) :
    i < tickLimit A ∧ j < tickLimit A := by
  by_contra hn
  have hs : tickLimit A ≤ i ∨ tickLimit A ≤ j := by omega
  rw [buildTable_outside_parent A v i j hs] at hp
  cases hp

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

private theorem dpValue_buildTable_selected_length (A : InnerInput) (v i j : ℕ)
    (hp : (buildTable A v i j).parent = .lengthTick) :
    dpValue A (buildTable A) v i j = dpValue A (buildTable A) v (i + 1) j := by
  by_cases hs : tickLimit A ≤ i ∨ tickLimit A ≤ j
  · have hs' : tickLimit A ≤ i + 1 ∨ tickLimit A ≤ j := by omega
    simp only [dpValue, if_pos hs, if_pos hs']
  by_cases hv : v ∈ activeVertices A.I
  · have hi : i < tickLimit A := by omega
    have hj : j < tickLimit A := by omega
    obtain ⟨T, _, hfinal⟩ := buildTable_layer_witness A i j hi hj
    have hhere := hfinal v i j (Or.inr ⟨rfl, le_rfl⟩)
    have hparent : (buildLayer A T i j v i j).parent = .lengthTick := by
      rw [← hhere]; exact hp
    have he := (buildLayer_selected_ticks A T i j v hv).1 hparent
    have hn := dpValue_congr_at A (buildTable A) (buildLayer A T i j) v (i + 1) j
      (hfinal v (i + 1) j (Or.inl (by omega)))
    rw [hn]
    simpa only [dpValue, if_neg hs, hhere] using he
  · rw [dpValue_buildTable_inactive A v i j hv,
      dpValue_buildTable_inactive A v (i + 1) j hv]

private theorem dpValue_buildTable_selected_cost (A : InnerInput) (v i j : ℕ)
    (hp : (buildTable A v i j).parent = .costTick) :
    dpValue A (buildTable A) v i j = dpValue A (buildTable A) v i (j + 1) := by
  by_cases hs : tickLimit A ≤ i ∨ tickLimit A ≤ j
  · have hs' : tickLimit A ≤ i ∨ tickLimit A ≤ j + 1 := by omega
    simp only [dpValue, if_pos hs, if_pos hs']
  by_cases hv : v ∈ activeVertices A.I
  · have hi : i < tickLimit A := by omega
    have hj : j < tickLimit A := by omega
    obtain ⟨T, _, hfinal⟩ := buildTable_layer_witness A i j hi hj
    have hhere := hfinal v i j (Or.inr ⟨rfl, le_rfl⟩)
    have hparent : (buildLayer A T i j v i j).parent = .costTick := by
      rw [← hhere]; exact hp
    have he := (buildLayer_selected_ticks A T i j v hv).2 hparent
    have hn := dpValue_congr_at A (buildTable A) (buildLayer A T i j) v i (j + 1)
      (hfinal v i (j + 1) (Or.inr ⟨rfl, by omega⟩))
    rw [hn]
    simpa only [dpValue, if_neg hs, hhere] using he
  · rw [dpValue_buildTable_inactive A v i j hv,
      dpValue_buildTable_inactive A v i (j + 1) hv]

private theorem buildTable_parent_rank (A : InnerInput) (v i j u : ℕ)
    (hp : (buildTable A v i j).parent = .edge u) :
    (buildTable A u i j).rank < (buildTable A v i j).rank := by
  obtain ⟨hi, hj⟩ := buildTable_edge_parent_nonsaturated A v i j u hp
  have hv : v ∈ activeVertices A.I :=
    activeVertices_edge_right A.I u v (buildTable_parent_edge_mem A v i j u hp)
  obtain ⟨T, _, hfinal⟩ := buildTable_layer_witness A i j hi hj
  have hhere := hfinal v i j (Or.inr ⟨rfl, le_rfl⟩)
  have hparent : (buildLayer A T i j v i j).parent = .edge u := by
    rw [← hhere]; exact hp
  rw [hhere, hfinal u i j (Or.inr ⟨rfl, le_rfl⟩)]
  exact buildLayer_parent_rank A T i j v u hv hparent

private theorem deterministic_retrieval (A : InnerInput) (t : ℕ) (ht : t < A.I.graph.n)
    (haccept : accepted A t) :
    ∃ S : RetrievalState, retrieve A t = some S ∧
      IsPath A.I.graph A.I.source t S.path ∧
      pathWeight A.I.length S.path ≤ (1 + A.δ) * A.L ∧
      pathWeight A.I.cost S.path ≤ (1 + A.δ) * A.I.budget := by
  clear ht
  exact deterministic_retrieval_of_table_facts A t haccept
    (buildTable_parent_ne_none A)
    (dpValue_buildTable_selected_length A)
    (dpValue_buildTable_selected_cost A)
    (dpValue_buildTable_selected_edge A)
    (buildTable_parent_edge_mem A)
    (buildTable_rank_le A)
    (buildTable_parent_rank A)

end NearLinearRSP.TwoResources
end

open NearLinearRSP.TwoResources

theorem solution (A : InnerInput) (t : ℕ) (ht : t < A.I.graph.n)
    (haccept : accepted A t) :
    ∃ P : List ℕ, IsPath A.I.graph A.I.source t P ∧
      pathWeight A.I.length P ≤ (1 + A.δ) * A.L ∧
      pathWeight A.I.cost P ≤ (1 + A.δ) * A.I.budget := by
  obtain ⟨S, _, hP, hL, hC⟩ := deterministic_retrieval A t ht haccept
  exact ⟨S.path, hP, hL, hC⟩
