-- Prove2me | solution 1 for MultiStoreAssort.Approx.tightness_instance
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T07:55:15.400334+00:00
-- url     : https://prove2.me/submissions/cec3da1a-2c31-4f1f-8e01-00b1ca9fd48a

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

lemma s_vals (ε : ℝ) (hε : 0 < ε) :
    MultiStoreAssort.SMR.single (![1 + 1 / ε, 1] : Fin 2 → ℝ) (![ε, 1 / ε] : Fin 2 → ℝ) ∅ = 0 ∧
    MultiStoreAssort.SMR.single (![1 + 1 / ε, 1] : Fin 2 → ℝ) (![ε, 1 / ε] : Fin 2 → ℝ) {0} = 1 ∧
    MultiStoreAssort.SMR.single (![1 + 1 / ε, 1] : Fin 2 → ℝ) (![ε, 1 / ε] : Fin 2 → ℝ) {1} = 1 / (1 + ε) ∧
    MultiStoreAssort.SMR.single (![1 + 1 / ε, 1] : Fin 2 → ℝ) (![ε, 1 / ε] : Fin 2 → ℝ) {0, 1} = 1 := by
  have hne : ε ≠ 0 := hε.ne'
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [MultiStoreAssort.SMR.single, ChoiceCDLP.MNL.mnlObjective]
  · simp [MultiStoreAssort.SMR.single, ChoiceCDLP.MNL.mnlObjective]
    field_simp
  · simp [MultiStoreAssort.SMR.single, ChoiceCDLP.MNL.mnlObjective]
    field_simp
  · simp [MultiStoreAssort.SMR.single, ChoiceCDLP.MNL.mnlObjective, Finset.sum_pair]
    field_simp
    ring

lemma sub_cases (S : Finset (Fin 2)) : S = ∅ ∨ S = {0} ∨ S = {1} ∨ S = {0, 1} := by
  revert S; decide

lemma stilde_iff (ε : ℝ) (hε : 0 < ε) (S : Finset (Fin 2)) :
    MultiStoreAssort.SMR.IsStilde (![1 + 1 / ε, 1] : Fin 2 → ℝ) (![ε, 1 / ε] : Fin 2 → ℝ) S ↔ S = {0} := by
  obtain ⟨h0, h1, h2, h3⟩ := s_vals ε hε
  have hq : 1 / (1 + ε) ≤ 1 := by
    rw [div_le_one (by linarith)]; linarith
  have hopt0 : MultiStoreAssort.SMR.IsOptSingle (![1 + 1 / ε, 1] : Fin 2 → ℝ) (![ε, 1 / ε] : Fin 2 → ℝ) {0} := by
    intro T
    rcases sub_cases T with rfl | rfl | rfl | rfl
    · rw [h0, h1]; norm_num
    · rw [h1]
    · rw [h2, h1]; exact hq
    · rw [h3, h1]
  have hrev0 : MultiStoreAssort.SMR.IsRevenueOrdered ({0} : Finset (Fin 2)) :=
    ⟨1, le_refl _, by norm_num, by decide⟩
  constructor
  · rintro ⟨⟨j, hj1, hj2, hS⟩, hopt, hmin⟩
    have hc := hmin {0} hrev0 hopt0
    interval_cases j
    · rw [hS]; decide
    · exfalso
      rw [hS] at hc
      revert hc; decide
  · rintro rfl
    refine ⟨hrev0, hopt0, ?_⟩
    intro T ⟨j, hj1, hj2, hT⟩ _
    have : (0 : Fin 2) ∈ T := by
      rw [hT]; simp [MultiStoreAssort.SMR.prefixSet]; omega
    exact Finset.card_pos.2 ⟨0, this⟩

open MultiStoreAssort.Approx MultiStoreAssort.SMR in
lemma rev_same (ε : ℝ) (hε : 0 < ε) :
    revQh (![1, 0] : Fin 2 → ℝ) (![1 + 1 / ε, 1] : Fin 2 → ℝ) (fun _ => (![ε, 1 / ε] : Fin 2 → ℝ))
      (fun _ _ _ => (0 : ℝ)) ![{0}, {0}] = 1 := by
  obtain ⟨h0, h1, h2, h3⟩ := s_vals ε hε
  unfold revQh
  rw [Fin.sum_univ_two, split_store]
  have hS : Sbar (![{0}, {0}] : Fin 2 → Finset (Fin 2)) = {0} := by decide
  rw [hS]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Finset.sdiff_self,
    Finset.sum_empty, zero_div, add_zero, zero_mul, one_mul]
  have : (∑ k ∈ ({0} : Finset (Fin 2)), (![1 + 1 / ε, 1] : Fin 2 → ℝ) k * (![ε, 1 / ε] : Fin 2 → ℝ) k) /
      (1 + ∑ l ∈ ({0} : Finset (Fin 2)), (![ε, 1 / ε] : Fin 2 → ℝ) l) =
      single (![1 + 1 / ε, 1] : Fin 2 → ℝ) (![ε, 1 / ε] : Fin 2 → ℝ) {0} := by
    unfold single ChoiceCDLP.MNL.mnlObjective
    rw [add_comm (∑ l ∈ ({0} : Finset (Fin 2)), (![ε, 1 / ε] : Fin 2 → ℝ) l) 1]
  rw [this, h1]

open MultiStoreAssort.Approx MultiStoreAssort.SMR in
lemma rev_diff (ε : ℝ) (hε : 0 < ε) :
    revQh (![1, 0] : Fin 2 → ℝ) (![1 + 1 / ε, 1] : Fin 2 → ℝ) (fun _ => (![ε, 1 / ε] : Fin 2 → ℝ))
      (fun _ _ _ => (0 : ℝ)) ![{0}, {1}] = 1 + 1 / ((1 + ε) * (1 + ε + ε ^ 2)) := by
  obtain ⟨h0, h1, h2, h3⟩ := s_vals ε hε
  have hne : ε ≠ 0 := hε.ne'
  unfold revQh
  rw [Fin.sum_univ_two, split_store]
  have hS : Sbar (![{0}, {1}] : Fin 2 → Finset (Fin 2)) = {0, 1} := by decide
  have hO : ({0, 1} : Finset (Fin 2)) \ {0} = {1} := by decide
  have hd : discFactor (fun (_ _ _ : Fin 2) => (0 : ℝ)) (![{0}, {1}] : Fin 2 → Finset (Fin 2)) 0 1 = 1 := by
    unfold discFactor
    have : (Finset.univ.filter (fun j : Fin 2 => (1 : Fin 2) ∈ (![{0}, {1}] : Fin 2 → Finset (Fin 2)) j)) = {1} := by
      decide
    rw [this]
    simp
  rw [hS]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, zero_mul, add_zero, one_mul]
  rw [hO]
  simp only [Finset.sum_singleton]
  rw [hd]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  have h1' : (1 + ε) ≠ 0 := by linarith
  have h2' : (1 + ε + ε ^ 2) ≠ 0 := by positivity
  have h3' : (1 + ε + 1 / ε * 1) ≠ 0 := by positivity
  field_simp
  ring

open MultiStoreAssort.Approx in
theorem solution (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) :
    let lam : Fin 2 → ℝ := ![1, 0]
    let r : Fin 2 → ℝ := ![1 + 1 / ε, 1]
    let v : Fin 2 → Fin 2 → ℝ := fun _ => ![ε, 1 / ε]
    let c : Fin 2 → Fin 2 → Fin 2 → ℝ := fun _ _ _ => 0
    (∀ (i : Fin 2) (S : Finset (Fin 2)), MultiStoreAssort.SMR.IsStilde r (v i) S ↔ S = {0}) ∧
      revQh lam r v c ![{0}, {0}] = 1 ∧
      revQh lam r v c ![{0}, {1}] = 1 + 1 / ((1 + ε) * (1 + ε + ε ^ 2)) := by
  intro lam r v c
  exact ⟨fun i S => stilde_iff ε hε0 S, rev_same ε hε0, rev_diff ε hε0⟩
