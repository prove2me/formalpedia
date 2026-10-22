-- Prove2me | solution 1 for MultiStoreAssort.Approx.second_inequality
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T07:19:01.778678+00:00
-- url     : https://prove2.me/submissions/44e847c1-7627-4358-8d07-00d7f256533c

import Mathlib
import Definitions.Def_ChoiceCDLP_MNL_mnlObjective
import Definitions.Def_MultiStoreAssort_Approx_Model

set_option autoImplicit false


lemma d1 {n : ℕ} (r v ε : Fin n → ℝ) (hv : ∀ i, 0 < v i)
    (hε : ∀ i, 0 ≤ ε i ∧ ε i ≤ 1) (T : Finset (Fin n)) :
    ∃ S : Finset (Fin n),
      MultiStoreAssort.SMR.single r (fun i => ε i * v i) T ≤ MultiStoreAssort.SMR.single r v S := by
  classical
  have hDpos : 0 < ∑ j ∈ T, ε j * v j + 1 := by
    have : 0 ≤ ∑ j ∈ T, ε j * v j :=
      Finset.sum_nonneg (fun j _ => (mul_nonneg (hε j).1 (hv j).le))
    linarith
  set R' : ℝ := MultiStoreAssort.SMR.single r (fun i => ε i * v i) T with hR'
  have hR'def : R' = (∑ j ∈ T, r j * (ε j * v j)) / (∑ j ∈ T, ε j * v j + 1) := rfl
  have key : R' * (∑ j ∈ T, ε j * v j + 1) = ∑ j ∈ T, r j * (ε j * v j) := by
    rw [hR'def]; field_simp
  have h1 : ∑ j ∈ T, ε j * v j * (r j - R') = R' := by
    have : ∑ j ∈ T, ε j * v j * (r j - R') =
        ∑ j ∈ T, r j * (ε j * v j) - R' * ∑ j ∈ T, ε j * v j := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl (fun j _ => by ring)
    rw [this]; linarith
  refine ⟨T.filter (fun j => R' < r j), ?_⟩
  have h2 : ∑ j ∈ T, ε j * v j * (r j - R') ≤
      ∑ j ∈ T.filter (fun j => R' < r j), v j * (r j - R') := by
    rw [Finset.sum_filter]
    apply Finset.sum_le_sum
    intro j hj
    by_cases h : R' < r j
    · rw [if_pos h]
      have hh : 0 < r j - R' := by linarith
      nlinarith [mul_nonneg (mul_nonneg (hv j).le (sub_nonneg.2 (hε j).2)) hh.le]
    · rw [if_neg h]
      have : r j - R' ≤ 0 := by linarith
      exact mul_nonpos_of_nonneg_of_nonpos (mul_nonneg (hε j).1 (hv j).le) this
  have hSpos : 0 < ∑ j ∈ T.filter (fun j => R' < r j), v j + 1 := by
    have : 0 ≤ ∑ j ∈ T.filter (fun j => R' < r j), v j :=
      Finset.sum_nonneg (fun j _ => (hv j).le)
    linarith
  have h3 : ∑ j ∈ T.filter (fun j => R' < r j), v j * (r j - R') =
      ∑ j ∈ T.filter (fun j => R' < r j), r j * v j -
        R' * ∑ j ∈ T.filter (fun j => R' < r j), v j := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun j _ => by ring)
  show R' ≤ (∑ j ∈ T.filter (fun j => R' < r j), r j * v j) /
      (∑ j ∈ T.filter (fun j => R' < r j), v j + 1)
  rw [le_div_iff₀ hSpos]
  nlinarith
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
    (hv : ∀ i k, 0 < v i k) (hc : ∀ i j k, 0 ≤ c i j k) (hcii : ∀ i k, c i i k = 0)
    (St : Fin m → Finset (Fin n)) (hSt : ∀ i, MultiStoreAssort.SMR.IsOptSingle r (v i) (St i)) :
    ∀ S : Fin m → Finset (Fin n),
      revQh lam r v c S ≤ 2 * ∑ i, lam i * MultiStoreAssort.SMR.single r (v i) (St i) := by
  classical
  intro S
  unfold revQh
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  have hper : ∑ k, r k * pQh v c S i k ≤ 2 * MultiStoreAssort.SMR.single r (v i) (St i) := by
    rw [split_store]
    set O := MultiStoreAssort.SMR.Sbar S \ S i with hO
    set B := ∑ l ∈ S i, v i l with hBdef
    set D := ∑ l ∈ O, v i l * MultiStoreAssort.SMR.discFactor c S i l with hDdef
    set C := ∑ k ∈ O, r k * (v i k * MultiStoreAssort.SMR.discFactor c S i k) with hCdef
    have hB : 0 ≤ B := Finset.sum_nonneg (fun l _ => (hv i l).le)
    have hD : 0 ≤ D :=
      Finset.sum_nonneg (fun l _ => mul_nonneg (hv i l).le (disc_nonneg c S i l))
    have hC : 0 ≤ C :=
      Finset.sum_nonneg (fun k _ => mul_nonneg (hrpos k).le
        (mul_nonneg (hv i k).le (disc_nonneg c S i k)))
    have hfirst : (∑ k ∈ S i, r k * v i k) / (1 + B) = MultiStoreAssort.SMR.single r (v i) (S i) := by
      unfold MultiStoreAssort.SMR.single ChoiceCDLP.MNL.mnlObjective
      rw [hBdef, add_comm 1]
    have h1 : MultiStoreAssort.SMR.single r (v i) (S i) ≤ MultiStoreAssort.SMR.single r (v i) (St i) :=
      hSt i (S i)
    have hsec : C / ((1 + B) * (1 + B + D)) ≤ C / (1 + D) := by
      apply div_le_div_of_nonneg_left hC (by linarith)
      nlinarith
    have hCD : C / (1 + D) =
        MultiStoreAssort.SMR.single r (fun k => MultiStoreAssort.SMR.discFactor c S i k * v i k) O := by
      unfold MultiStoreAssort.SMR.single ChoiceCDLP.MNL.mnlObjective
      rw [hCdef, hDdef, add_comm 1]
      congr 1
      · exact Finset.sum_congr rfl (fun k _ => by ring)
      · congr 1
        exact Finset.sum_congr rfl (fun k _ => by ring)
    obtain ⟨S', hS'⟩ := d1 r (v i) (fun k => MultiStoreAssort.SMR.discFactor c S i k) (hv i)
      (fun k => ⟨disc_nonneg c S i k, disc_le_one c hc S i k⟩) O
    have h2 : MultiStoreAssort.SMR.single r (v i) S' ≤ MultiStoreAssort.SMR.single r (v i) (St i) :=
      hSt i S'
    rw [hfirst]
    have := hCD ▸ hsec
    linarith
  calc lam i * ∑ k, r k * pQh v c S i k ≤ lam i * (2 * MultiStoreAssort.SMR.single r (v i) (St i)) :=
        mul_le_mul_of_nonneg_left hper (hlam i)
    _ = 2 * (lam i * MultiStoreAssort.SMR.single r (v i) (St i)) := by ring
