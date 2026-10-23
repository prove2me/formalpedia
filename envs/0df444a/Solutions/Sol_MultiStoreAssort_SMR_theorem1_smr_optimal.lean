-- Prove2me | solution 1 for MultiStoreAssort.SMR.theorem1_smr_optimal
-- status  : ACCEPTED   (prove)
-- author  : @frknbls
-- created : 2026-10-22T17:05:58.489296+00:00
-- url     : https://prove2.me/submissions/256f61d8-e99c-4da4-aebb-4f895745b301

import Definitions.Def_MultiStoreAssort_SMR_Model
namespace MultiStoreAssort.SMR

open Finset

lemma discFactor_nonneg {m n : ℕ} (c : Fin m → Fin m → Fin n → ℝ) (S : Fin m → Finset (Fin n))
    (i : Fin m) (k : Fin n) : 0 ≤ discFactor c S i k := by
  unfold discFactor
  exact NNReal.coe_nonneg _

lemma discFactor_le_one {m n : ℕ} (c : Fin m → Fin m → Fin n → ℝ) (hc : ∀ i j k, 0 ≤ c i j k)
    (S : Fin m → Finset (Fin n)) (i : Fin m) (k : Fin n) : discFactor c S i k ≤ 1 := by
  unfold discFactor
  have h : ((Finset.univ.filter (fun j => k ∈ S j)).sup
      (fun j => (Real.exp (-(c i j k))).toNNReal)) ≤ 1 := by
    apply Finset.sup_le
    intro j _
    have h1 : Real.exp (-(c i j k)) ≤ 1 := by
      rw [Real.exp_le_one_iff]; linarith [hc i j k]
    have := Real.toNNReal_le_toNNReal h1
    simpa using this
  exact_mod_cast h

/-- Fractional relaxation bound for the MNL objective. -/
lemma frac_bound {n : ℕ} (r v : Fin n → ℝ) (hv : ∀ k, 0 < v k) (R : ℝ)
    (hR : ∀ T, single r v T ≤ R) (x : Fin n → ℝ) (hx0 : ∀ k, 0 ≤ x k) (hx1 : ∀ k, x k ≤ 1) :
    ∑ k, r k * (v k * x k) ≤ R * (1 + ∑ k, v k * x k) := by
  set T0 := Finset.univ.filter (fun k => R < r k) with hT0
  have hT := hR T0
  unfold single ChoiceCDLP.MNL.mnlObjective at hT
  have hpos : 0 < ∑ j ∈ T0, v j + 1 := by
    have : 0 ≤ ∑ j ∈ T0, v j := Finset.sum_nonneg (fun j _ => (hv j).le)
    linarith
  rw [div_le_iff₀ hpos] at hT
  have key : ∑ k, (r k - R) * (v k * x k) ≤ ∑ k ∈ T0, (r k - R) * v k := by
    rw [hT0, Finset.sum_filter]
    apply Finset.sum_le_sum
    intro k _
    split_ifs with h
    · have := hv k
      have : (r k - R) * (v k * x k) ≤ (r k - R) * (v k * 1) := by
        apply mul_le_mul_of_nonneg_left _ (by linarith)
        exact mul_le_mul_of_nonneg_left (hx1 k) this.le
      simpa using this
    · push_neg at h
      have : 0 ≤ v k * x k := mul_nonneg (hv k).le (hx0 k)
      nlinarith
  have e1 : ∑ k, (r k - R) * (v k * x k) = ∑ k, r k * (v k * x k) - R * ∑ k, v k * x k := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl; intro k _; ring
  have e2 : ∑ k ∈ T0, (r k - R) * v k = ∑ k ∈ T0, r k * v k - R * ∑ k ∈ T0, v k := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl; intro k _; ring
  rw [e1] at key; rw [e2] at key
  have e3 : ∑ j ∈ T0, r j * v j = ∑ j ∈ T0, r j * v j := rfl
  nlinarith

lemma storeRev_le {m n : ℕ} (r v : Fin n → ℝ) (hv : ∀ k, 0 < v k)
    (c : Fin m → Fin m → Fin n → ℝ) (hc : ∀ i j k, 0 ≤ c i j k) (R : ℝ)
    (hR : ∀ T, single r v T ≤ R) (S : Fin m → Finset (Fin n)) (i : Fin m) :
    storeRevM r v c S i ≤ R := by
  classical
  set x : Fin n → ℝ := fun k => if k ∈ S i then 1 else if k ∈ Sbar S \ S i then
    discFactor c S i k else 0 with hx
  have hx0 : ∀ k, 0 ≤ x k := by
    intro k; simp only [hx]; split_ifs
    · norm_num
    · exact discFactor_nonneg c S i k
    · norm_num
  have hx1 : ∀ k, x k ≤ 1 := by
    intro k; simp only [hx]; split_ifs
    · norm_num
    · exact discFactor_le_one c hc S i k
    · norm_num
  have hD : denomM v c S i = 1 + ∑ k, v k * x k := by
    unfold denomM
    have : ∀ k, v k * x k = (if k ∈ S i then v k else 0) +
        (if k ∈ Sbar S \ S i then v k * discFactor c S i k else 0) := by
      intro k; simp only [hx]
      by_cases h1 : k ∈ S i
      · have : k ∉ Sbar S \ S i := by simp [h1]
        simp [h1, this]
      · simp [h1]
    simp_rw [this, Finset.sum_add_distrib, Finset.sum_ite_mem, Finset.univ_inter]
    ring
  have hpM : ∀ k, pM v c S i k = v k * x k / denomM v c S i := by
    intro k; unfold pM; simp only [hx]
    split_ifs <;> simp
  have hDpos : 0 < denomM v c S i := by
    rw [hD]
    have : 0 ≤ ∑ k, v k * x k := Finset.sum_nonneg (fun k _ => mul_nonneg (hv k).le (hx0 k))
    linarith
  have hS : storeRevM r v c S i = (∑ k, r k * (v k * x k)) / denomM v c S i := by
    unfold storeRevM
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl; intro k _
    rw [hpM]; ring
  rw [hS, div_le_iff₀ hDpos, hD]
  exact frac_bound r v hv R hR x hx0 hx1

lemma storeRev_const {m n : ℕ} (r v : Fin n → ℝ) (c : Fin m → Fin m → Fin n → ℝ)
    (St : Finset (Fin n)) (i : Fin m) :
    storeRevM r v c (fun _ => St) i = single r v St := by
  classical
  have hsb : Sbar (fun _ : Fin m => St) \ St = ∅ := by
    rw [Finset.sdiff_eq_empty_iff_subset]
    unfold Sbar
    exact Finset.sup_le (fun _ _ => le_refl _)
  unfold storeRevM single ChoiceCDLP.MNL.mnlObjective
  have hp : ∀ k, pM v c (fun _ => St) i k = if k ∈ St then v k / denomM v c (fun _ => St) i
      else 0 := by
    intro k; unfold pM; simp [hsb]
  have hd : denomM v c (fun _ => St) i = ∑ j ∈ St, v j + 1 := by
    unfold denomM; simp [hsb]; ring
  simp_rw [hp, hd, mul_ite, mul_zero, Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_div]
  apply Finset.sum_congr rfl; intro k _; ring

theorem theorem1_smr_optimal {m n : ℕ} (lam : Fin m → ℝ) (r v : Fin n → ℝ)
    (c : Fin m → Fin m → Fin n → ℝ)
    (hlam : ∀ i, 0 ≤ lam i) (hlam1 : ∑ i, lam i = 1) (hr : StrictAnti r) (hrpos : ∀ k, 0 < r k)
    (hv : ∀ k, 0 < v k) (hc : ∀ i j k, 0 ≤ c i j k) (hcii : ∀ i k, c i i k = 0)
    (St : Finset (Fin n)) (hSt : IsStilde r v St) :
    ∀ S : Fin m → Finset (Fin n), revM lam r v c S ≤ revM lam r v c (fun _ => St) := by
  intro S
  unfold revM
  apply Finset.sum_le_sum
  intro i _
  apply mul_le_mul_of_nonneg_left _ (hlam i)
  rw [storeRev_const]
  exact storeRev_le r v hv c hc _ hSt.2.1 S i

end MultiStoreAssort.SMR


-- Platform entry point: restates the target verbatim.
namespace MultiStoreAssort.SMR

/-- Theorem 1, p. 11: the optimal solution to the SMR problem is `S* = (S̃, S̃, …, S̃)`. -/
theorem _root_.solution {m n : ℕ} (lam : Fin m → ℝ) (r v : Fin n → ℝ)
    (c : Fin m → Fin m → Fin n → ℝ)
    (hlam : ∀ i, 0 ≤ lam i) (hlam1 : ∑ i, lam i = 1) (hr : StrictAnti r) (hrpos : ∀ k, 0 < r k)
    (hv : ∀ k, 0 < v k) (hc : ∀ i j k, 0 ≤ c i j k) (hcii : ∀ i k, c i i k = 0)
    (St : Finset (Fin n)) (hSt : IsStilde r v St) :
    ∀ S : Fin m → Finset (Fin n), revM lam r v c S ≤ revM lam r v c (fun _ => St) := by
  apply @MultiStoreAssort.SMR.theorem1_smr_optimal <;> assumption

end MultiStoreAssort.SMR
