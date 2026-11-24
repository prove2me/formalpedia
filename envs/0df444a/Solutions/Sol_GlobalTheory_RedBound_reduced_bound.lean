-- Prove2me | solution 1 for GlobalTheory.RedBound.reduced_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T21:40:09.333821+00:00
-- url     : https://prove2.me/submissions/620d3fb5-416d-4f70-91a5-2274c7c67336

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_AdelicPair
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_UnipotentUpperInvUpperTriangularBoundedStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_SiegelReducedIntegralFormBoundedEntries
import Theorems.Thm_GlobalTheory_RedBound_entry_bound
import Theorems.Thm_GlobalTheory_RedBound_orth_entry_le
import Theorems.Thm_GlobalTheory_RedBound_prod_le
import Theorems.Thm_GlobalTheory_T_unipotent_upper_inv_upperTriangular_bounded


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix GlobalTheory.ClassFin
open GlobalTheory GlobalTheory.RedBound
namespace GlobalTheory.RedBound
theorem _root_.solution : ∀ (N : ℕ) (C R : ℝ), ∃ C' : ℝ, ∀ (k : Matrix (Fin N) (Fin N) ℝ) (a : Fin N → ℝ)
    (n : Matrix (Fin N) (Fin N) ℝ), IsSiegel C k a n → ∀ (X : Matrix (Fin N) (Fin N) ℝ)
    (B B' : Matrix (Fin N) (Fin N) ℤ) (μ : ℝ), μ ≠ 0 → |μ| ≤ R → (∀ i j, |X i j| ≤ R) →
    B.map (Int.cast : ℤ → ℝ) = (k * diagonal a * n)ᵀ * X * (k * diagonal a * n) →
    (k * diagonal a * n) * B'.map (Int.cast : ℤ → ℝ) * (k * diagonal a * n)ᵀ = μ • X →
    ∀ i j, |(B i j : ℝ)| ≤ C' := by
  intro N C R
  obtain ⟨M, hM⟩ := GlobalTheory.T.unipotent_upper_inv_upperTriangular_bounded N C
  obtain ⟨Cm, hCm1, hCC⟩ : ∃ Cm : ℝ, 1 ≤ Cm ∧ C ≤ Cm := ⟨max C 1, le_max_right _ _, le_max_left _ _⟩
  obtain ⟨M₀, hM₀, hMM⟩ : ∃ M₀ : ℝ, 0 ≤ M₀ ∧ M ≤ M₀ := ⟨max M 0, le_max_right _ _, le_max_left _ _⟩
  obtain ⟨R₀, hR₀, hRR⟩ : ∃ R₀ : ℝ, 0 ≤ R₀ ∧ R ≤ R₀ := ⟨max R 0, le_max_right _ _, le_max_left _ _⟩
  obtain ⟨R', hR'⟩ : ∃ R' : ℝ, R' = N * N * (1 * R₀ * 1) := ⟨_, rfl⟩
  obtain ⟨K₁, hK₁⟩ : ∃ K₁ : ℝ, K₁ = M₀ * (Cm ^ 2 * (R₀ * R')) * M₀ := ⟨_, rfl⟩
  obtain ⟨T, hT⟩ : ∃ T : ℝ, T = N * N * K₁ + 1 := ⟨_, rfl⟩
  have hCm0 : 0 < Cm := lt_of_lt_of_le one_pos hCm1
  have hR'0 : 0 ≤ R' := by rw [hR']; positivity
  have hK₁0 : 0 ≤ K₁ := by rw [hK₁]; positivity
  have hT0 : 0 < T := by rw [hT]; positivity
  refine ⟨N * N * (Cm * (Cm ^ 2 * T * R') * Cm), ?_⟩
  intro k a n hS X B B' μ hμ hμR hX hB hB' i j
  obtain ⟨m, hmn, _hnm, hmlow, hmb⟩ := hM n hS.diag hS.lower hS.bdd
  have hmb' : ∀ p q, |m p q| ≤ M₀ := fun p q => (hmb p q).trans hMM
  have hnb : ∀ p q, |n p q| ≤ Cm := fun p q => (hS.bdd p q).trans hCC
  have hμ₀ : |μ| ≤ R₀ := hμR.trans hRR
  have hk : ∀ p q, |k p q| ≤ 1 := orth_entry_le k hS.orth
  obtain ⟨X', hX'def⟩ : ∃ X', X' = kᵀ * X * k := ⟨_, rfl⟩
  have hX' : ∀ p q, |X' p q| ≤ R' := by
    intro p q
    rw [hX'def, hR']
    apply entry_bound
    intro r s
    rw [abs_mul, abs_mul, Matrix.transpose_apply]
    exact mul_le_mul (mul_le_mul (hk r p) ((hX r s).trans hRR) (abs_nonneg _) zero_le_one)
      (hk s q) (abs_nonneg _) (by positivity)
  obtain ⟨Br', hBr'⟩ : ∃ Br', Br' = B'.map (Int.cast : ℤ → ℝ) := ⟨_, rfl⟩
  obtain ⟨W, hWdef⟩ : ∃ W, W = n * Br' * nᵀ := ⟨_, rfl⟩
  have hWeq : diagonal a * W * diagonal a = μ • X' := by
    have h1 : kᵀ * ((k * diagonal a * n) * Br' * (k * diagonal a * n)ᵀ) * k = μ • X' := by
      rw [hBr', hB', hX'def, Matrix.mul_smul, Matrix.smul_mul]
    rw [← h1, hWdef]
    have h2 : kᵀ * ((k * diagonal a * n) * Br' * (k * diagonal a * n)ᵀ) * k =
        (kᵀ * k) * (diagonal a * (n * Br' * nᵀ) * diagonal a) * (kᵀ * k) := by
      simp only [Matrix.transpose_mul, Matrix.diagonal_transpose, Matrix.mul_assoc]
    rw [h2, hS.orth, Matrix.one_mul, Matrix.mul_one]
  have hWent : ∀ p q, a p * W p q * a q = μ * X' p q := by
    intro p q
    have := congrFun (congrFun hWeq p) q
    simpa [Matrix.mul_diagonal, Matrix.diagonal_mul] using this
  have hBm : Br' = m * W * mᵀ := by
    rw [hWdef]
    calc Br' = (m * n) * Br' * (m * n)ᵀ := by rw [hmn]; simp
      _ = m * (n * Br' * nᵀ) * mᵀ := by rw [Matrix.transpose_mul]; simp only [Matrix.mul_assoc]
  have hZ : B.map (Int.cast : ℤ → ℝ) = nᵀ * (diagonal a * X' * diagonal a) * n := by
    rw [hB, hX'def]
    simp only [Matrix.transpose_mul, Matrix.diagonal_transpose, Matrix.mul_assoc]
  have hA : ∀ p q, T ≤ a p * a q → B' p q = 0 := by
    intro p q hpq
    have hpos : 0 < a p * a q := mul_pos (hS.pos p) (hS.pos q)
    have hb : |Br' p q| ≤ N * N * (K₁ / (a p * a q)) := by
      rw [hBm]
      apply entry_bound
      intro r s
      rw [le_div_iff₀ hpos, Matrix.transpose_apply]
      by_cases hr : r < p
      · rw [hmlow p r hr]; simp; positivity
      by_cases hs : s < q
      · rw [hmlow q s hs]; simp; positivity
      push_neg at hr hs
      have hWb : |W r s| * (a r * a s) ≤ R₀ * R' := by
        calc |W r s| * (a r * a s) = |a r * W r s * a s| := by
              rw [abs_mul, abs_mul, abs_of_pos (hS.pos r), abs_of_pos (hS.pos s)]; ring
          _ = |μ| * |X' r s| := by rw [hWent r s, abs_mul]
          _ ≤ R₀ * R' := mul_le_mul hμ₀ (hX' r s) (abs_nonneg _) hR₀
      have hapq := prod_le hS hCm1 hCC hr hs
      rw [abs_mul, abs_mul, hK₁]
      calc |m p r| * |W r s| * |m q s| * (a p * a q)
          ≤ |m p r| * |W r s| * |m q s| * (Cm ^ 2 * (a r * a s)) :=
            mul_le_mul_of_nonneg_left hapq (by positivity)
        _ = |m p r| * (Cm ^ 2 * (|W r s| * (a r * a s))) * |m q s| := by ring
        _ ≤ M₀ * (Cm ^ 2 * (R₀ * R')) * M₀ :=
            mul_le_mul (mul_le_mul (hmb' p r) (mul_le_mul_of_nonneg_left hWb (by positivity))
              (mul_nonneg (sq_nonneg _) (mul_nonneg (abs_nonneg _) (mul_pos (hS.pos r) (hS.pos s)).le)) hM₀) (hmb' q s) (abs_nonneg _) (by positivity)
    have hlt : |Br' p q| < 1 := by
      have e : (N : ℝ) * N * (K₁ / (a p * a q)) = (N * N * K₁) / (a p * a q) := by ring
      rw [e] at hb
      exact hb.trans_lt ((div_lt_one hpos).mpr (by linarith))
    have h3 : |((B' p q : ℤ) : ℝ)| < 1 := by rw [hBr'] at hlt; simpa using hlt
    have h4 : |B' p q| < 1 := by exact_mod_cast h3
    exact Int.abs_lt_one_iff.mp h4
  have hBz : ∀ p q, Cm ^ 2 * T ≤ a p * a q → W p q = 0 := by
    intro p q h
    rw [hWdef]
    simp only [Matrix.mul_apply, Matrix.transpose_apply]
    apply Finset.sum_eq_zero
    intro s _
    rw [Finset.sum_mul]
    apply Finset.sum_eq_zero
    intro r _
    by_cases hr : r < p
    · rw [hS.lower p r hr]; ring
    by_cases hs : s < q
    · rw [hS.lower q s hs]; ring
    push_neg at hr hs
    have hapq := prod_le hS hCm1 hCC hr hs
    have hT' : T ≤ a r * a s := by
      have : Cm ^ 2 * T ≤ Cm ^ 2 * (a r * a s) := h.trans hapq
      exact le_of_mul_le_mul_left this (by positivity)
    have h0 := hA r s hT'
    simp [hBr', h0]
  have hZb : ∀ p q, |a p * X' p q * a q| ≤ Cm ^ 2 * T * R' := by
    intro p q
    by_cases h : Cm ^ 2 * T ≤ a p * a q
    · have e := hWent p q
      rw [hBz p q h] at e
      have h0 : μ * X' p q = 0 := by rw [← e]; ring
      have hx : X' p q = 0 := (mul_eq_zero.mp h0).resolve_left hμ
      rw [hx]; simp; positivity
    · push_neg at h
      calc |a p * X' p q * a q| = (a p * a q) * |X' p q| := by
            rw [abs_mul, abs_mul, abs_of_pos (hS.pos p), abs_of_pos (hS.pos q)]; ring
        _ ≤ (Cm ^ 2 * T) * R' := mul_le_mul h.le (hX' p q) (abs_nonneg _) (by positivity)
  have hBe : (B i j : ℝ) = (nᵀ * (diagonal a * X' * diagonal a) * n) i j := by
    rw [← hZ]; simp
  rw [hBe]
  apply entry_bound
  intro r s
  have hZe : (diagonal a * X' * diagonal a) r s = a r * X' r s * a s := by
    simp [Matrix.mul_diagonal, Matrix.diagonal_mul]
  rw [Matrix.transpose_apply, hZe, abs_mul, abs_mul]
  exact mul_le_mul (mul_le_mul (hnb r i) (hZb r s) (abs_nonneg _) hCm0.le) (hnb s j)
    (abs_nonneg _) (by positivity)
end GlobalTheory.RedBound
