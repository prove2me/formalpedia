-- Prove2me | solution 1 for MultiStoreAssort.Approx.first_inequality
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T07:19:00.2756+00:00
-- url     : https://prove2.me/submissions/0cf52ad9-e53b-4b31-8deb-0ab2007a7593

import Mathlib
import Definitions.Def_ChoiceCDLP_MNL_mnlObjective
import Definitions.Def_MultiStoreAssort_Approx_Model

set_option autoImplicit false

open MultiStoreAssort.Approx MultiStoreAssort.SMR in
lemma split_store {m n : ℕ} (r : Fin n → ℝ) (v : Fin m → Fin n → ℝ)
    (c : Fin m → Fin m → Fin n → ℝ) (S : Fin m → Finset (Fin n)) (i : Fin m) :
    ∑ k, r k * pQh v c S i k =
      (∑ k ∈ S i, r k * v i k) / (1 + ∑ l ∈ S i, v i l) +
      (∑ k ∈ Sbar S \ S i, r k * (v i k * (discFactor c S i k))) /
        ((1 + ∑ l ∈ S i, v i l) *
          (1 + ∑ l ∈ S i, v i l + ∑ l ∈ Sbar S \ S i, v i l * discFactor c S i l)) := by
  classical
  have hpt : ∀ k, r k * pQh v c S i k =
      (if k ∈ S i then r k * v i k / (1 + ∑ l ∈ S i, v i l) else 0) +
      (if k ∈ Sbar S \ S i then r k * (v i k * discFactor c S i k) /
        ((1 + ∑ l ∈ S i, v i l) *
          (1 + ∑ l ∈ S i, v i l + ∑ l ∈ Sbar S \ S i, v i l * discFactor c S i l)) else 0) := by
    intro k
    by_cases h1 : k ∈ S i
    · have h2 : k ∉ Sbar S \ S i := by simp [h1]
      simp only [pQh, h1, h2, if_true, if_false, add_zero]
      ring
    · by_cases h2 : k ∈ Sbar S \ S i
      · simp only [pQh, h1, h2, if_true, if_false, zero_add]
        ring
      · simp [pQh, h1, h2]
  simp_rw [hpt]
  rw [Finset.sum_add_distrib, Finset.sum_ite_mem, Finset.sum_ite_mem, Finset.univ_inter,
    Finset.univ_inter, ← Finset.sum_div, ← Finset.sum_div]

lemma disc_nonneg {m n : ℕ} (c : Fin m → Fin m → Fin n → ℝ) (S : Fin m → Finset (Fin n))
    (i : Fin m) (k : Fin n) : 0 ≤ MultiStoreAssort.SMR.discFactor c S i k := by
  unfold MultiStoreAssort.SMR.discFactor
  exact NNReal.coe_nonneg _

lemma disc_le_one {m n : ℕ} (c : Fin m → Fin m → Fin n → ℝ) (hc : ∀ i j k, 0 ≤ c i j k)
    (S : Fin m → Finset (Fin n)) (i : Fin m) (k : Fin n) :
    MultiStoreAssort.SMR.discFactor c S i k ≤ 1 := by
  unfold MultiStoreAssort.SMR.discFactor
  have : ((Finset.univ.filter (fun j => k ∈ S j)).sup
      (fun j => (Real.exp (-(c i j k))).toNNReal)) ≤ 1 := by
    apply Finset.sup_le
    intro j _
    rw [Real.toNNReal_le_one]
    rw [Real.exp_le_one_iff]
    linarith [hc i j k]
  exact_mod_cast this

open MultiStoreAssort.Approx in
theorem solution {m n : ℕ} (lam : Fin m → ℝ) (r : Fin n → ℝ) (v : Fin m → Fin n → ℝ)
    (c : Fin m → Fin m → Fin n → ℝ)
    (hlam : ∀ i, 0 ≤ lam i) (hlam1 : ∑ i, lam i = 1) (hr : StrictAnti r) (hrpos : ∀ k, 0 < r k)
    (hv : ∀ i k, 0 < v i k) (hc : ∀ i j k, 0 ≤ c i j k) (hcii : ∀ i k, c i i k = 0) :
    ∀ T : Fin m → Finset (Fin n),
      ∑ i, lam i * MultiStoreAssort.SMR.single r (v i) (T i) ≤ revQh lam r v c T := by
  classical
  intro T
  unfold revQh
  apply Finset.sum_le_sum
  intro i _
  apply mul_le_mul_of_nonneg_left _ (hlam i)
  rw [split_store]
  have hB : 0 ≤ ∑ l ∈ T i, v i l := Finset.sum_nonneg (fun l _ => (hv i l).le)
  have hD : 0 ≤ ∑ l ∈ MultiStoreAssort.SMR.Sbar T \ T i, v i l * MultiStoreAssort.SMR.discFactor c T i l :=
    Finset.sum_nonneg (fun l _ => mul_nonneg (hv i l).le (disc_nonneg c T i l))
  have hC : 0 ≤ ∑ k ∈ MultiStoreAssort.SMR.Sbar T \ T i,
      r k * (v i k * MultiStoreAssort.SMR.discFactor c T i k) :=
    Finset.sum_nonneg (fun k _ => mul_nonneg (hrpos k).le (mul_nonneg (hv i k).le (disc_nonneg c T i k)))
  have hsecond : 0 ≤ (∑ k ∈ MultiStoreAssort.SMR.Sbar T \ T i,
      r k * (v i k * MultiStoreAssort.SMR.discFactor c T i k)) /
        ((1 + ∑ l ∈ T i, v i l) *
          (1 + ∑ l ∈ T i, v i l + ∑ l ∈ MultiStoreAssort.SMR.Sbar T \ T i,
            v i l * MultiStoreAssort.SMR.discFactor c T i l)) :=
    div_nonneg hC (mul_nonneg (by linarith) (by linarith))
  have hfirst : MultiStoreAssort.SMR.single r (v i) (T i) =
      (∑ k ∈ T i, r k * v i k) / (1 + ∑ l ∈ T i, v i l) := by
    unfold MultiStoreAssort.SMR.single ChoiceCDLP.MNL.mnlObjective
    rw [add_comm (∑ l ∈ T i, v i l) 1]
  linarith
