-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.actualRowCount_real_bound
-- status  : ACCEPTED   (prove)
-- author  : @polylog
-- created : 2026-10-20T18:18:32.859318+00:00
-- url     : https://prove2.me/submissions/f64a7f2d-aa8a-4b71-a4e5-d1a905b43802

import Definitions.Def_OAI_NumberTheory_PiExponent_Analysis_AnalyticAggregate_RemainderData

open scoped BigOperators Topology
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction

theorem solution {nu : ℝ} (d : OAI.PiExponent.DeterminantContradiction.FixedData nu) (H : ℝ)
    (hH : 0 ≤ H) :
    (OAI.PiExponent.DeterminantContradiction.actualRowCount d H : ℝ) ≤
      (d.K : ℝ) * (H / (d.v0 : ℝ) + 1) * (H + 1) ^ d.m := by
  classical
  let q : Fin d.m → ℕ := finiteDenominators d
  let w : Fin (d.m + 1) → ℝ :=
    InterpolationMatrix.rowWeights (d.v0 : ℝ) (d.base.theta : ℝ) (MatrixArithmetic.logWeights q)
  have hq2 : ∀ i : Fin d.m, 2 ≤ q i := fun i => (d.approximations i.val).1
  have hlognat : ∀ i : Fin d.m, 0 < ⌈Real.log (q i : ℝ)⌉₊ := by
    intro i
    rw [Nat.ceil_pos]
    apply Real.log_pos
    have h : (1 : ℕ) < q i := by have := hq2 i; omega
    exact_mod_cast h
  have hlog1 : ∀ i : Fin d.m, (1 : ℝ) ≤ MatrixArithmetic.logWeights q i := by
    intro i
    change (1 : ℝ) ≤ (⌈Real.log (q i : ℝ)⌉₊ : ℝ)
    have h : (1 : ℕ) ≤ ⌈Real.log (q i : ℝ)⌉₊ := hlognat i
    exact_mod_cast h
  have hθpos : 0 < (d.base.theta : ℝ) := d.base.theta_pos
  have hθ1 : (d.base.theta : ℝ) < 1 :=
    lt_trans d.base.theta_lt_A (lt_trans d.base.A_lt_B d.base.B_lt_one)
  have hw0 : w 0 = (d.v0 : ℝ) := by
    simp [w, InterpolationMatrix.rowWeights]
  have hwsucc : ∀ i : Fin d.m,
      w i.succ = MatrixArithmetic.logWeights q i / (d.base.theta : ℝ) := by
    intro i
    simp [w, InterpolationMatrix.rowWeights]
  -- Step 1: the row count factors as `K * card(strict simplex)`.
  have hcard : (actualRowCount d H : ℝ) = (d.K : ℝ) * ((strictWeightedSimplex w H).card : ℝ) := by
    have hNat : actualRowCount d H = d.K * (strictWeightedSimplex w H).card := by
      rw [actualRowCount]
      change Fintype.card (Fin d.K × ↥(strictWeightedSimplex w H)) =
        d.K * (strictWeightedSimplex w H).card
      simp
    rw [hNat]
    push_cast
    ring
  -- Step 2: the strict simplex sits inside a pi-finset box.
  have hsub1 : strictWeightedSimplex w H ⊆ realWeightedSimplex w H := by
    intro a ha
    simp only [strictWeightedSimplex, Finset.mem_filter] at ha
    exact ha.1
  have hsub2 : realWeightedSimplex w H ⊆
      Fintype.piFinset (fun i : Fin (d.m + 1) => Finset.range (⌊H / w i⌋₊ + 1)) := by
    intro a ha
    simp only [realWeightedSimplex, Finset.mem_filter] at ha
    exact ha.1
  have hcardle : (strictWeightedSimplex w H).card ≤
      (Fintype.piFinset (fun i : Fin (d.m + 1) => Finset.range (⌊H / w i⌋₊ + 1))).card :=
    Finset.card_le_card (hsub1.trans hsub2)
  have hprod : (Fintype.piFinset
        (fun i : Fin (d.m + 1) => Finset.range (⌊H / w i⌋₊ + 1))).card =
      ∏ i : Fin (d.m + 1), (⌊H / w i⌋₊ + 1) := by
    rw [Fintype.card_piFinset]
    simp
  -- Step 3: bound the number of box points by the product of coordinate ranges.
  have hS : ((strictWeightedSimplex w H).card : ℝ) ≤
      (H / (d.v0 : ℝ) + 1) * (H + 1) ^ d.m := by
    have hfac0 : ((⌊H / w 0⌋₊ : ℕ) : ℝ) + 1 ≤ H / (d.v0 : ℝ) + 1 := by
      have hpos0 : 0 < w 0 := by rw [hw0]; exact d.v0_pos
      have hfloor : ((⌊H / w 0⌋₊ : ℕ) : ℝ) ≤ H / w 0 :=
        Nat.floor_le (div_nonneg hH hpos0.le)
      rw [hw0] at hfloor ⊢
      linarith
    have hfacsucc : ∀ i : Fin d.m, ((⌊H / w i.succ⌋₊ : ℕ) : ℝ) + 1 ≤ H + 1 := by
      intro i
      have hw1 : (1 : ℝ) ≤ w i.succ := by
        rw [hwsucc i]
        rw [le_div_iff₀ hθpos]
        linarith [hlog1 i, hθ1]
      have hwpos : 0 < w i.succ := lt_of_lt_of_le zero_lt_one hw1
      have hfloor : ((⌊H / w i.succ⌋₊ : ℕ) : ℝ) ≤ H / w i.succ :=
        Nat.floor_le (div_nonneg hH hwpos.le)
      have hdiv : H / w i.succ ≤ H := div_le_self hH hw1
      linarith
    have hprodle : (∏ i : Fin d.m, (((⌊H / w i.succ⌋₊ : ℕ) : ℝ) + 1)) ≤
        (H + 1) ^ d.m := by
      calc (∏ i : Fin d.m, (((⌊H / w i.succ⌋₊ : ℕ) : ℝ) + 1))
          ≤ ∏ _ : Fin d.m, (H + 1) := by
            apply Finset.prod_le_prod
            · intro i _
              positivity
            · intro i _
              exact hfacsucc i
        _ = (H + 1) ^ d.m := by
            simp
    have h1 : ((strictWeightedSimplex w H).card : ℝ) ≤
        ∏ i : Fin (d.m + 1), (((⌊H / w i⌋₊ : ℕ) : ℝ) + 1) := by
      have h2 : ((strictWeightedSimplex w H).card : ℝ) ≤
          ((Fintype.piFinset (fun i : Fin (d.m + 1) =>
            Finset.range (⌊H / w i⌋₊ + 1))).card : ℝ) := by
        exact_mod_cast hcardle
      rw [hprod] at h2
      push_cast at h2
      exact h2
    rw [Fin.prod_univ_succ] at h1
    refine h1.trans (mul_le_mul hfac0 hprodle ?_ ?_)
    · positivity
    · have hv0 : (0 : ℝ) < (d.v0 : ℝ) := d.v0_pos
      have hnn : 0 ≤ H / (d.v0 : ℝ) := div_nonneg hH hv0.le
      linarith
  -- Step 4: multiply by `K ≥ 0` and rearrange.
  rw [hcard]
  have hKnn : (0 : ℝ) ≤ (d.K : ℝ) := Nat.cast_nonneg d.K
  calc (d.K : ℝ) * ((strictWeightedSimplex w H).card : ℝ)
      ≤ (d.K : ℝ) * ((H / (d.v0 : ℝ) + 1) * (H + 1) ^ d.m) :=
        mul_le_mul_of_nonneg_left hS hKnn
    _ = (d.K : ℝ) * (H / (d.v0 : ℝ) + 1) * (H + 1) ^ d.m := by ring
