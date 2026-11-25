-- Prove2me | solution 1 for NearLinearRSP.TwoResources.potential_detects_violation
-- status  : ACCEPTED   (prove)
-- author  : @k-variant
-- created : 2026-11-25T10:41:57.338915+00:00
-- url     : https://prove2.me/submissions/151b7d47-1b65-4a5c-88e5-b4d41cbdca66

import Theorems.Thm_NearLinearRSP_TwoResources_Implementation_initialization_and_expectation_correct

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

section
namespace NearLinearRSP.TwoResources
open scoped BigOperators

theorem dpValue_buildTable_nonneg :
  ∀ (A : InnerInput) (v i j : ℕ),
  0 ≤ dpValue A (buildTable A) v i j :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.1.2.2.2.1.2.1.1

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

open NearLinearRSP.TwoResources

theorem solution (A : InnerInput) (t : ℕ) (ht : t < A.I.graph.n)
    (S : RetrievalState) (houtput : retrieve A t = some S) :
    (pathWeight A.I.length S.path > (1 + A.δ) * A.L → S.i < tickLimit A →
      1 ≤ potential A S) ∧
    (pathWeight A.I.cost S.path > (1 + A.δ) * A.I.budget → S.j < tickLimit A →
      1 ≤ potential A S) := by
  exact potential_detects_violation_of_nonneg A S
    (dpValue_buildTable_nonneg A S.front S.i S.j)
