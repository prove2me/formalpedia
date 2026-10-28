-- Prove2me | solution 2 for MultiStoreAssort.Approx.proposition7_half_approx
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-27T14:24:28.2745+00:00
-- url     : https://prove2.me/submissions/2bcf4d04-3378-4a37-83d5-79677a701254

import Mathlib
import Definitions.Def_ChoiceCDLP_MNL_mnlObjective
import Definitions.Def_MultiStoreAssort_Approx_Model
import Theorems.Thm_MultiStoreAssort_Approx_first_inequality
import Theorems.Thm_MultiStoreAssort_Approx_second_inequality

-- carved verbatim out of submission a029e158-d79e-45a1-acb0-5aa7a2e78ba6, lines 276-343

section
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
theorem solution :
    (∀ (m n : ℕ) (lam : Fin m → ℝ) (r : Fin n → ℝ) (v : Fin m → Fin n → ℝ)
        (c : Fin m → Fin m → Fin n → ℝ),
        (∀ i, 0 ≤ lam i) → ∑ i, lam i = 1 → StrictAnti r → (∀ k, 0 < r k) →
        (∀ i k, 0 < v i k) → (∀ i j k, 0 ≤ c i j k) → (∀ i k, c i i k = 0) →
        ∀ St : Fin m → Finset (Fin n), (∀ i, MultiStoreAssort.SMR.IsStilde r (v i) (St i)) →
          ∀ S : Fin m → Finset (Fin n), (1 / 2) * revQh lam r v c S ≤ revQh lam r v c St) ∧
    (∀ δ : ℝ, 0 < δ →
      ∃ (lam : Fin 2 → ℝ) (r : Fin 2 → ℝ) (v : Fin 2 → Fin 2 → ℝ) (c : Fin 2 → Fin 2 → Fin 2 → ℝ),
        (∀ i, 0 ≤ lam i) ∧ ∑ i, lam i = 1 ∧ StrictAnti r ∧ (∀ k, 0 < r k) ∧
        (∀ i k, 0 < v i k) ∧ (∀ i j k, 0 ≤ c i j k) ∧ (∀ i k, c i i k = 0) ∧
        (∃ St : Fin 2 → Finset (Fin 2), ∀ i, MultiStoreAssort.SMR.IsStilde r (v i) (St i)) ∧
        ∀ St : Fin 2 → Finset (Fin 2), (∀ i, MultiStoreAssort.SMR.IsStilde r (v i) (St i)) →
          ∃ S : Fin 2 → Finset (Fin 2), revQh lam r v c St < (1 / 2 + δ) * revQh lam r v c S) := by
  refine ⟨?_, ?_⟩
  · intro m n lam r v c hlam hlam1 hr hrpos hv hc hcii St hSt S
    have h2 := MultiStoreAssort.Approx.second_inequality lam r v c hlam hlam1 hr hrpos hv hc hcii St (fun i => (hSt i).2.1) S
    have h1 := MultiStoreAssort.Approx.first_inequality lam r v c hlam hlam1 hr hrpos hv hc hcii St
    linarith
  · intro δ hδ
    set ε : ℝ := δ / (5 + 10 * δ) with hε
    have hden : 0 < 5 + 10 * δ := by linarith
    have hε0 : 0 < ε := div_pos hδ hden
    have hεδ : ε ≤ δ / 5 := by
      rw [hε, div_le_div_iff₀ hden (by norm_num)]
      nlinarith
    have hε1 : ε < 1 := by
      rw [hε, div_lt_one hden]; linarith
    refine ⟨![1, 0], ![1 + 1 / ε, 1], fun _ => ![ε, 1 / ε], fun _ _ _ => 0,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro i; fin_cases i <;> simp
    · simp [Fin.sum_univ_two]
    · rw [Fin.strictAnti_iff_succ_lt]
      intro i
      fin_cases i
      simp
      positivity
    · intro k; fin_cases k <;> simp <;> positivity
    · intro i k; fin_cases k <;> simp <;> positivity
    · intro i j k; simp
    · intro i k; simp
    · exact ⟨fun _ => {0}, fun i => (stilde_iff ε hε0 _).2 rfl⟩
    · intro St hSt
      have h0 := (stilde_iff ε hε0 _).1 (hSt 0)
      have h1 := (stilde_iff ε hε0 _).1 (hSt 1)
      have hSt' : St = ![{0}, {0}] := by
        funext i; fin_cases i
        · simpa using h0
        · simpa using h1
      refine ⟨![{0}, {1}], ?_⟩
      rw [hSt', rev_same ε hε0, rev_diff ε hε0]
      have e2 : ε ^ 2 ≤ ε := by nlinarith
      have e3 : ε ^ 3 ≤ ε := by nlinarith [e2, hε0]
      have hprod : (1 + ε) * (1 + ε + ε ^ 2) ≤ 1 + δ := by
        have : (1 + ε) * (1 + ε + ε ^ 2) = 1 + 2 * ε + 2 * ε ^ 2 + ε ^ 3 := by ring
        linarith
      have hq : 1 / (1 + δ) ≤ 1 / ((1 + ε) * (1 + ε + ε ^ 2)) :=
        one_div_le_one_div_of_le (by positivity) hprod
      have hδ1 : 0 < 1 + δ := by linarith
      have hkey : 1 < (1 / 2 + δ) * (1 + 1 / (1 + δ)) := by
        have : (1 / 2 + δ) * (1 + 1 / (1 + δ)) = (1 / 2 + δ) * (2 + δ) / (1 + δ) := by
          field_simp; ring
        rw [this, lt_div_iff₀ hδ1]
        nlinarith [sq_nonneg δ]
      calc (1 : ℝ) < (1 / 2 + δ) * (1 + 1 / (1 + δ)) := hkey
        _ ≤ (1 / 2 + δ) * (1 + 1 / ((1 + ε) * (1 + ε + ε ^ 2))) :=
          mul_le_mul_of_nonneg_left (by linarith) (by positivity)

end
