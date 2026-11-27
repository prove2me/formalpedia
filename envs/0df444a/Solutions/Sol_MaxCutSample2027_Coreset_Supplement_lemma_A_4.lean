-- Prove2me | solution 1 for MaxCutSample2027.Coreset.Supplement.lemma_A_4
-- status  : ACCEPTED   (prove)
-- author  : @DavidDenisov
-- created : 2026-11-27T00:57:56.644854+00:00
-- url     : https://prove2.me/submissions/7f1e9377-8086-4f56-9b2b-43635659223f

import Definitions.Def_MaxCutSample2027_Coreset_Supplement_sampling
open scoped BigOperators
noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 550000

open MaxCutSample2027
open MaxCutSample2027.Coreset
open MaxCutSample2027.Coreset.Supplement

private theorem sign_column_exp (m r : ℕ) (a : Fin m → Fin r → ℝ) (j : Fin r) (t : ℝ) :
    matrixSignAverage m r (fun σ => Real.exp (t * ∑ i, signValue (σ i j) * a i j)) ≤
      Real.exp (t ^ 2 * (∑ i, a i j ^ 2) / 2) := by
  classical
  let f (i : Fin m) (l : Fin r) (b : Bool) : ℝ :=
    Real.exp (if l = j then t * (signValue b * a i l) else 0) / 2
  have normalize (σ : Fin m → Fin r → Bool) :
      (∏ i, ∏ l, f i l (σ i l)) =
        Real.exp (t * ∑ i, signValue (σ i j) * a i j) / (2 : ℝ) ^ (m * r) := by
    unfold f
    simp only [Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
      ← Real.exp_sum]
    rw [← pow_mul, Nat.mul_comm r m]
    congr 1
    simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true, Finset.mul_sum]
  have part (i : Fin m) : (∑ row : Fin r → Bool, ∏ l, f i l (row l)) =
      Real.cosh (t * a i j) := by
    rw [← Fintype.prod_sum (f i), Finset.prod_eq_single j]
    · simp only [f, Fintype.sum_bool, signValue, if_true, Bool.false_eq_true,
        if_false, one_mul, neg_one_mul, Real.cosh_eq, mul_neg]
      ring
    · intro l _ hl
      simp [f, hl]
    · simp
  calc
    _ = ∑ σ : Fin m → Fin r → Bool, ∏ i, ∏ l, f i l (σ i l) := by
      unfold matrixSignAverage
      rw [Finset.sum_div]
      exact Finset.sum_congr rfl fun σ _ => (normalize σ).symm
    _ = ∏ i, ∑ row : Fin r → Bool, ∏ l, f i l (row l) :=
      (Fintype.prod_sum (fun i (row : Fin r → Bool) => ∏ l, f i l (row l))).symm
    _ = ∏ i, Real.cosh (t * a i j) := Finset.prod_congr rfl fun i _ => part i
    _ ≤ ∏ i, Real.exp ((t * a i j) ^ 2 / 2) :=
      Finset.prod_le_prod (fun i _ => (Real.cosh_pos _).le) (fun i _ => Real.cosh_le_exp_half_sq _)
    _ = _ := by
      rw [← Real.exp_sum]
      congr 1
      simp only [Finset.sum_div, Finset.mul_sum]
      congr 1
      funext i
      ring

private theorem matrix_sign_weights (m r : ℕ) :
    (∑ _ : Fin m → Fin r → Bool, ((2 : ℝ) ^ (m * r))⁻¹) = 1 := by
  have h : (Fintype.card (Fin m → Fin r → Bool) : ℝ) = (2 : ℝ) ^ (m * r) := by
    simp [Fintype.card_bool, pow_mul, Nat.mul_comm m r]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, h]
  exact mul_inv_cancel₀ (by positivity)

theorem solution (m r : ℕ) (hm : 1 ≤ m) (hr : 1 ≤ r) (a : Fin m → Fin r → ℝ) :
    matrixSignAverage m r (fun σ => sSup (Set.range (fun j : Fin r =>
      |∑ i, signValue (σ i j) * a i j|))) ≤
    Real.sqrt (2 * Real.log (2 * (r : ℝ))) *
      sSup (Set.range (fun j : Fin r => Real.sqrt (∑ i, a i j ^ 2))) := by
  classical
  let _ : Nonempty (Fin r) := ⟨⟨0, by omega⟩⟩
  let S (σ : Fin m → Fin r → Bool) (j : Fin r) := ∑ i, signValue (σ i j) * a i j
  let U (σ : Fin m → Fin r → Bool) := sSup (Set.range (fun j => |S σ j|))
  let B := sSup (Set.range (fun j : Fin r => Real.sqrt (∑ i, a i j ^ 2)))
  let E := matrixSignAverage m r U
  let R : ℝ := 2 * (r : ℝ)
  have hR : 1 < R := by
    have : (1 : ℝ) ≤ r := by exact_mod_cast hr
    dsimp [R]
    linarith
  have Bcol (j : Fin r) : Real.sqrt (∑ i, a i j ^ 2) ≤ B :=
    le_csSup (Set.finite_range _).bddAbove ⟨j, rfl⟩
  have Bn : 0 ≤ B := (Real.sqrt_nonneg _).trans (Bcol (Classical.choice inferInstance))
  have sq_col (j : Fin r) : (∑ i, a i j ^ 2) ≤ B ^ 2 := by
    have hs : 0 ≤ ∑ i, a i j ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
    rw [← Real.sq_sqrt hs]
    exact pow_le_pow_left₀ (Real.sqrt_nonneg _) (Bcol j) 2
  change E ≤ Real.sqrt (2 * Real.log R) * B
  rcases Bn.eq_or_lt with hB | hB
  · have zero_entry (i : Fin m) (j : Fin r) : a i j = 0 := by
      have hc := sq_col j
      rw [← hB] at hc
      have hi := Finset.single_le_sum (f := fun i => a i j ^ 2)
        (fun i _ => sq_nonneg (a i j)) (Finset.mem_univ i)
      have hsq : a i j ^ 2 ≤ 0 := hi.trans (by simpa using hc)
      nlinarith
    have hU (σ) : U σ = 0 := by simp [U, S, zero_entry]
    simp [E, matrixSignAverage, hU, ← hB]
  · have hlog : 0 < Real.log R := Real.log_pos hR
    let H := Real.sqrt (2 * Real.log R)
    have hH : 0 < H := Real.sqrt_pos.2 (by positivity)
    have Hsq : H ^ 2 = 2 * Real.log R := Real.sq_sqrt (by positivity)
    let t := H / B
    have ht : 0 < t := div_pos hH hB
    have mgf (j : Fin r) (u : ℝ) :
        matrixSignAverage m r (fun σ => Real.exp (u * S σ j)) ≤
          Real.exp (u ^ 2 * B ^ 2 / 2) := by
      refine (sign_column_exp m r a j u).trans (Real.exp_le_exp.mpr ?_)
      exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (sq_col j) (sq_nonneg _)) (by norm_num)
    have mgf_max (σ) : Real.exp (t * U σ) ≤
        ∑ j, (Real.exp (t * S σ j) + Real.exp (-t * S σ j)) := by
      have hn : (Set.range (fun j => |S σ j|)).Nonempty := Set.range_nonempty _
      obtain ⟨j, hj⟩ := hn.csSup_mem (Set.finite_range _)
      have h₁ : Real.exp (t * U σ) ≤ Real.exp (t * S σ j) + Real.exp (-t * S σ j) := by
        change |S σ j| = U σ at hj
        rw [← hj, abs_eq_max_neg]
        rcases le_total (S σ j) (-S σ j) with h | h
        · rw [max_eq_right h]
          rw [mul_neg, neg_mul]
          exact le_add_of_nonneg_left (Real.exp_pos _).le
        · rw [max_eq_left h]
          exact le_add_of_nonneg_right (Real.exp_pos _).le
      exact h₁.trans (Finset.single_le_sum (f := fun k => Real.exp (t * S σ k) + Real.exp (-t * S σ k))
        (fun k _ => by positivity) (Finset.mem_univ j))
    have jensen :
        Real.exp (t * E) ≤ matrixSignAverage m r (fun σ => Real.exp (t * U σ)) := by
      let w : ℝ := ((2 : ℝ) ^ (m * r))⁻¹
      have hw : 0 ≤ w := by dsimp [w]; positivity
      have hj := convexOn_exp.map_sum_le (t := Finset.univ)
        (w := fun _ : Fin m → Fin r → Bool => w) (p := fun σ => t * U σ)
        (fun _ _ => hw) (matrix_sign_weights m r) (fun _ _ => Set.mem_univ _)
      have lhs : (∑ σ : Fin m → Fin r → Bool, w • (t * U σ)) = t * E := by
        simp only [E, matrixSignAverage, smul_eq_mul, div_eq_mul_inv, Finset.mul_sum, Finset.sum_mul]
        exact Finset.sum_congr rfl fun σ _ => by dsimp [w]; ring
      have rhs : (∑ σ : Fin m → Fin r → Bool, w • Real.exp (t * U σ)) =
          matrixSignAverage m r (fun σ => Real.exp (t * U σ)) := by
        unfold matrixSignAverage
        rw [Finset.sum_div]
        simp only [smul_eq_mul, div_eq_mul_inv]
        exact Finset.sum_congr rfl fun σ _ => mul_comm _ _
      rwa [lhs, rhs] at hj
    have aggregate :
        matrixSignAverage m r (fun σ => Real.exp (t * U σ)) ≤
          R * Real.exp (t ^ 2 * B ^ 2 / 2) := by
      calc
        _ ≤ matrixSignAverage m r
            (fun σ => ∑ j, (Real.exp (t * S σ j) + Real.exp (-t * S σ j))) := by
          unfold matrixSignAverage
          exact div_le_div_of_nonneg_right (Finset.sum_le_sum fun σ _ => mgf_max σ) (by positivity)
        _ = ∑ j, (matrixSignAverage m r (fun σ => Real.exp (t * S σ j)) +
            matrixSignAverage m r (fun σ => Real.exp (-t * S σ j))) := by
          simp only [matrixSignAverage]
          rw [Finset.sum_comm, Finset.sum_div]
          simp only [Finset.sum_add_distrib, add_div]
        _ ≤ ∑ _ : Fin r, (Real.exp (t ^ 2 * B ^ 2 / 2) + Real.exp (t ^ 2 * B ^ 2 / 2)) := by
          apply Finset.sum_le_sum
          intro j _
          apply add_le_add (mgf j t)
          simpa only [neg_sq] using mgf j (-t)
        _ = _ := by simp [R, nsmul_eq_mul]; ring
    have bound := jensen.trans aggregate
    rw [← Real.exp_log (zero_lt_one.trans hR), ← Real.exp_add, Real.exp_le_exp] at bound
    have htB : t * B = H := div_mul_cancel₀ H hB.ne'
    have hquad : t ^ 2 * B ^ 2 / 2 = Real.log R := by
      rw [← mul_pow, htB, Hsq]
      ring
    rw [hquad] at bound
    apply le_of_mul_le_mul_left _ ht
    change t * E ≤ t * (H * B)
    rw [mul_left_comm t H B, htB, ← pow_two, Hsq]
    linarith
