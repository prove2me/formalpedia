-- Prove2me | solution 1 for LassoDantzig.Dantzig.eq_B25
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T01:35:33.445275+00:00
-- url     : https://prove2.me/submissions/e495eef0-247b-4325-9564-0ee7078ca14c

import Mathlib
import Definitions.Def_LassoDantzig_Dantzig_Model

namespace LassoDantzig.Dantzig

theorem aux_b25_colNorm {n M : ℕ} (X : Matrix (Fin n) (Fin M) ℝ)
    (hdiag : ∀ j, (1 / (n : ℝ)) * ∑ i, X i j ^ 2 = 1) (j : Fin M) : colNorm X j = 1 := by
  unfold colNorm; rw [hdiag j, Real.sqrt_one]

theorem aux_b25_l1_le {M : ℕ} (δ : Fin M → ℝ) (J : Finset (Fin M)) :
    l1On δ J ≤ Real.sqrt J.card * l2On δ J := by
  unfold l1On l2On
  rw [← Real.sqrt_mul (Nat.cast_nonneg _)]
  have h := Finset.sum_mul_sq_le_sq_mul_sq J (fun _ => (1:ℝ)) (fun j => |δ j|)
  simp only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one, sq_abs] at h
  exact le_trans (le_abs_self _) (Real.abs_le_sqrt h)

theorem aux_b25_quad {n M : ℕ} (X : Matrix (Fin n) (Fin M) ℝ) (δ : Fin M → ℝ) :
    (1 / (n : ℝ)) * ∑ i, X.mulVec δ i ^ 2 =
      ∑ j, δ j * ((1 / (n : ℝ)) * ∑ i, X i j * X.mulVec δ i) := by
  have hi : ∀ i, X.mulVec δ i ^ 2 = ∑ j, δ j * (X i j * X.mulVec δ i) := by
    intro i
    have h1 : X.mulVec δ i = ∑ j, X i j * δ j := rfl
    rw [sq]
    nth_rewrite 1 [h1]
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [Finset.sum_congr rfl (fun i _ => hi i), Finset.sum_comm, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

end LassoDantzig.Dantzig

open LassoDantzig.Dantzig

theorem solution {n M : ℕ} (hn : 1 ≤ n) (X : Matrix (Fin n) (Fin M) ℝ)
    (hdiag : ∀ j, (1 / (n : ℝ)) * ∑ i, X i j ^ 2 = 1)
    (βstar : Fin M → ℝ) (s : ℕ) (hsparse : sparsity βstar ≤ s)
    (w : Fin n → ℝ) (r : ℝ) (hB : NoiseEvent X r w)
    (βD : Fin M → ℝ) (hD : IsDantzig X (fun i => X.mulVec βstar i + w i) r βD) :
    InLambda X (fun i => X.mulVec βstar i + w i) r βstar ∧
    (∀ j : Fin M, |(1 / (n : ℝ)) * ∑ i, X i j * X.mulVec (βD - βstar) i| ≤ 2 * r) ∧
    ConeCond 1 (supp βstar) (βD - βstar) ∧
    (1 / (n : ℝ)) * ∑ i, X.mulVec (βD - βstar) i ^ 2 ≤
      4 * r * Real.sqrt s * l2On (βD - βstar) (supp βstar) := by
  have hBr : ∀ j : Fin M, |(1 / (n : ℝ)) * ∑ i, X i j * w i| ≤ r := by
    intro j
    have := hB j
    rwa [aux_b25_colNorm X hdiag j, mul_one] at this
  -- β* ∈ Λ
  have hLam : InLambda X (fun i => X.mulVec βstar i + w i) r βstar := by
    intro j
    have hw : ∀ i, (X.mulVec βstar i + w i - X.mulVec βstar i) = w i := fun i => by ring
    simp only [hw]
    exact hBr j
  -- (i)
  have hI : ∀ j : Fin M, |(1 / (n : ℝ)) * ∑ i, X i j * X.mulVec (βD - βstar) i| ≤ 2 * r := by
    intro j
    have key : (1 / (n : ℝ)) * ∑ i, X i j * X.mulVec (βD - βstar) i =
        (1 / (n : ℝ)) * ∑ i, X i j * w i -
          (1 / (n : ℝ)) * ∑ i, X i j * ((X.mulVec βstar i + w i) - X.mulVec βD i) := by
      rw [← mul_sub, ← Finset.sum_sub_distrib]
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      rw [Matrix.mulVec_sub]
      simp only [Pi.sub_apply]
      ring
    rw [key]
    have h1 := hBr j
    have h2 := hD.1 j
    calc _ ≤ |(1 / (n : ℝ)) * ∑ i, X i j * w i| +
          |(1 / (n : ℝ)) * ∑ i, X i j * ((X.mulVec βstar i + w i) - X.mulVec βD i)| :=
          abs_sub _ _
      _ ≤ r + r := add_le_add h1 h2
      _ = 2 * r := by ring
  -- (ii) cone condition
  have hmin := hD.2 βstar hLam
  have hcompl : ∀ j ∈ (supp βstar)ᶜ, βstar j = 0 := by
    intro j hj
    simpa [supp] using hj
  have hCone : ConeCond 1 (supp βstar) (βD - βstar) := by
    unfold ConeCond l1On
    rw [one_mul]
    have e1 := Finset.sum_add_sum_compl (supp βstar) (fun j => |βD j|)
    have e2 := Finset.sum_add_sum_compl (supp βstar) (fun j => |βstar j|)
    have e3 : ∑ j ∈ (supp βstar)ᶜ, |βstar j| = 0 := by
      apply Finset.sum_eq_zero
      intro j hj
      rw [hcompl j hj, abs_zero]
    have e4 : ∑ j ∈ (supp βstar)ᶜ, |(βD - βstar) j| = ∑ j ∈ (supp βstar)ᶜ, |βD j| := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [Pi.sub_apply, hcompl j hj, sub_zero]
    have e5 : ∑ j ∈ supp βstar, |βstar j| ≤
        ∑ j ∈ supp βstar, |βD j| + ∑ j ∈ supp βstar, |(βD - βstar) j| := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_le_sum
      intro j _
      rw [Pi.sub_apply]
      have : βstar j = βD j - (βD j - βstar j) := by ring
      calc |βstar j| = |βD j - (βD j - βstar j)| := by rw [← this]
        _ ≤ |βD j| + |βD j - βstar j| := abs_sub _ _
    linarith
  refine ⟨hLam, hI, hCone, ?_⟩
  -- prediction bound
  set δ := βD - βstar with hδ
  by_cases hr : 0 ≤ r
  · rw [aux_b25_quad X δ]
    have step1 : ∑ j, δ j * ((1 / (n : ℝ)) * ∑ i, X i j * X.mulVec δ i) ≤
        ∑ j, |δ j| * (2 * r) := by
      apply Finset.sum_le_sum
      intro j _
      calc δ j * ((1 / (n : ℝ)) * ∑ i, X i j * X.mulVec δ i)
          ≤ |δ j * ((1 / (n : ℝ)) * ∑ i, X i j * X.mulVec δ i)| := le_abs_self _
        _ = |δ j| * |(1 / (n : ℝ)) * ∑ i, X i j * X.mulVec δ i| := abs_mul _ _
        _ ≤ |δ j| * (2 * r) := mul_le_mul_of_nonneg_left (hI j) (abs_nonneg _)
    have step2 : ∑ j, |δ j| = l1On δ (supp βstar) + l1On δ (supp βstar)ᶜ := by
      unfold l1On
      rw [Finset.sum_add_sum_compl]
    have hc : l1On δ (supp βstar)ᶜ ≤ l1On δ (supp βstar) := by
      have := hCone
      unfold ConeCond at this
      linarith
    have step3 := aux_b25_l1_le δ (supp βstar)
    have hsq : Real.sqrt ((supp βstar).card : ℝ) ≤ Real.sqrt (s : ℝ) := by
      apply Real.sqrt_le_sqrt
      exact_mod_cast hsparse
    have hl2 : 0 ≤ l2On δ (supp βstar) := Real.sqrt_nonneg _
    have step4 : l1On δ (supp βstar) ≤ Real.sqrt s * l2On δ (supp βstar) :=
      le_trans step3 (mul_le_mul_of_nonneg_right hsq hl2)
    rw [← Finset.sum_mul, step2] at step1
    calc _ ≤ (l1On δ (supp βstar) + l1On δ (supp βstar)ᶜ) * (2 * r) := step1
      _ ≤ (2 * l1On δ (supp βstar)) * (2 * r) := by
          apply mul_le_mul_of_nonneg_right _ (by linarith)
          linarith
      _ = 4 * r * l1On δ (supp βstar) := by ring
      _ ≤ 4 * r * (Real.sqrt s * l2On δ (supp βstar)) :=
          mul_le_mul_of_nonneg_left step4 (by linarith)
      _ = 4 * r * Real.sqrt s * l2On δ (supp βstar) := by ring
  · have hE : IsEmpty (Fin M) := ⟨fun j => by
      have := hBr j
      have := abs_nonneg ((1 / (n : ℝ)) * ∑ i, X i j * w i)
      exact hr (by linarith)⟩
    rw [aux_b25_quad X δ]
    have hS : supp βstar = ∅ := Finset.eq_empty_of_isEmpty _
    simp [l2On, hS]
