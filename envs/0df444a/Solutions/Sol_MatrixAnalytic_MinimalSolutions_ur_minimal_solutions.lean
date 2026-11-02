-- Prove2me | solution 1 for MatrixAnalytic.MinimalSolutions.ur_minimal_solutions
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T14:08:56.632197+00:00
-- url     : https://prove2.me/submissions/7b77a7ff-f5b8-43e8-9ac8-fb882af059ac

import Mathlib
import Theorems.Thm_MatrixAnalytic_MinimalSolutions_UG_minimal
import Theorems.Thm_MatrixAnalytic_MinimalSolutions_linear_progression
import Theorems.Thm_MatrixAnalytic_MinimalSolutions_ur_path_factorization
import Definitions.Def_MatrixAnalytic_MinimalSolutions_Chain
import Definitions.Def_MatrixAnalytic_MinimalSolutions_QBD
import Definitions.Def_MatrixAnalytic_MinimalSolutions_Passage

open scoped ENNReal
open MatrixAnalytic.MinimalSolutions

lemma urm_mm_assoc {ι : Type*} (X Y Z : ι → ι → ℝ≥0∞) :
    matMulE (matMulE X Y) Z = matMulE X (matMulE Y Z) := by
  funext i j; unfold matMulE; simp_rw [← ENNReal.tsum_mul_right, ← ENNReal.tsum_mul_left]
  rw [ENNReal.tsum_comm]; refine tsum_congr fun a => tsum_congr fun b => ?_; ring

lemma urm_mm_add_left {ι : Type*} (X Y Z : ι → ι → ℝ≥0∞) :
    matMulE (X + Y) Z = matMulE X Z + matMulE Y Z := by
  funext i j; unfold matMulE; simp only [Pi.add_apply, add_mul, ENNReal.tsum_add]

lemma urm_mm_add_right {ι : Type*} (X Y Z : ι → ι → ℝ≥0∞) :
    matMulE X (Y + Z) = matMulE X Y + matMulE X Z := by
  funext i j; unfold matMulE; simp only [Pi.add_apply, mul_add, ENNReal.tsum_add]

lemma urm_mm_one {ι : Type*} [DecidableEq ι] (X : ι → ι → ℝ≥0∞) : matMulE X matOneE = X := by
  funext i j
  unfold matMulE matOneE
  rw [tsum_eq_single j (by intro b hb; simp [hb])]
  simp

lemma urm_S_right {α : Type*} [DecidableEq α] (U : α → α → ℝ≥0∞) :
    seriesInvE U = matOneE + matMulE (seriesInvE U) U := by
  funext i j; unfold seriesInvE; rw [tsum_eq_zero_add' ENNReal.summable]
  simp only [Pi.add_apply]; congr 1
  show ∑' n, matMulE (matPowE U n) U i j = _
  unfold matMulE; simp_rw [← ENNReal.tsum_mul_right]; rw [ENNReal.tsum_comm]

lemma urm_mm_mono {ι : Type*} (X X' Y Y' : ι → ι → ℝ≥0∞) (hX : ∀ i j, X i j ≤ X' i j)
    (hY : ∀ i j, Y i j ≤ Y' i j) : ∀ i j, matMulE X Y i j ≤ matMulE X' Y' i j := by
  intro i j; unfold matMulE; exact ENNReal.tsum_le_tsum fun k => mul_le_mul' (hX i k) (hY k j)

lemma urm_S_mono {ι : Type*} [DecidableEq ι] (U W : ι → ι → ℝ≥0∞) (h : ∀ i j, U i j ≤ W i j) :
    ∀ i j, seriesInvE U i j ≤ seriesInvE W i j := by
  have hp : ∀ n i j, matPowE U n i j ≤ matPowE W n i j := by
    intro n; induction n with
    | zero => intro i j; exact le_rfl
    | succ n ih => intro i j; exact urm_mm_mono (matPowE U n) (matPowE W n) U W ih h i j
  intro i j; exact ENNReal.tsum_le_tsum fun n => hp n i j

lemma urm_super_S {ι : Type*} [DecidableEq ι] (a z w : ι → ι → ℝ≥0∞)
    (h : ∀ i j, a i j + matMulE z w i j ≤ z i j) : ∀ i j, matMulE a (seriesInvE w) i j ≤ z i j := by
  let q (K : ℕ) : ι → ι → ℝ≥0∞ := fun i j => ∑ n ∈ Finset.range K, matPowE w n i j
  have hk : ∀ K i j, matMulE a (q K) i j ≤ z i j := by
    intro K; induction K with
    | zero => intro i j; simp [q, matMulE]
    | succ K ih =>
      intro i j
      have e : q (K + 1) = matOneE + matMulE (q K) w := by
        funext k l; change (∑ n ∈ Finset.range (K + 1), matPowE w n k l) = _
        rw [Finset.sum_range_succ']; simp only [q, matPowE, Pi.add_apply]; rw [add_comm]; congr 1
        unfold matMulE; rw [← Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
        simp_rw [Finset.sum_mul]
      rw [e, urm_mm_add_right, urm_mm_one, ← urm_mm_assoc]
      have hm := urm_mm_mono (matMulE a (q K)) z w w ih (fun _ _ => le_rfl) i j
      exact le_trans (add_le_add (le_rfl : a i j ≤ a i j) hm) (h i j)
  intro i j
  have e : matMulE a (seriesInvE w) i j = ∑' n, matMulE a (matPowE w n) i j := by
    unfold matMulE seriesInvE; simp_rw [← ENNReal.tsum_mul_left]; rw [ENNReal.tsum_comm]
  rw [e]; refine ENNReal.tsum_le_of_sum_range_le fun K => le_trans (le_of_eq ?_) (hk K i j)
  unfold matMulE q; rw [← Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
  simp_rw [Finset.mul_sum]

/-- `U` lies below every supersolution of (8.14), via the iterates `U(k)` of Theorem 8.1.1. -/
lemma urm_U_le_super {ι : Type*} [Countable ι] [DecidableEq ι]
    (B A₀ A₁ A₂ : ι → ι → ℝ)
    (hP : IsStochasticC (qbdP B A₀ A₁ A₂))
    (hirr : IrreducibleC (qbdP B A₀ A₁ A₂)) (X : ι → ι → ℝ≥0∞)
    (hX : ∀ i j, (ennMat A₁ + matMulE (ennMat A₀) (matMulE (seriesInvE X) (ennMat A₂))) i j ≤ X i j) :
    ∀ i j, matU (qbdP B A₀ A₁ A₂) i j ≤ X i j := by
  set P := qbdP B A₀ A₁ A₂ with hPdef
  rcases linear_progression B A₀ A₁ A₂ hP hirr with ⟨hU1, hUnext, hGk, _hMono, hUlim, _hGlim⟩
  have hSeq : ∀ k, 1 ≤ k → ∀ i j, matUk P k i j ≤ X i j := by
    intro k hk
    induction k, hk using Nat.le_induction with
    | base =>
      intro i j; rw [hU1]
      exact le_trans (le_add_of_nonneg_right (zero_le)) (hX i j)
    | succ n hn ih =>
      intro i j
      rw [hUnext n hn, (hGk n hn).2]
      refine le_trans ?_ (hX i j)
      simp only [Pi.add_apply]
      refine add_le_add le_rfl ?_
      refine urm_mm_mono _ _ _ _ (fun _ _ => le_rfl) ?_ i j
      exact urm_mm_mono _ _ _ _ (urm_S_mono _ _ ih) (fun _ _ => le_rfl)
  intro i j
  exact le_of_tendsto (hUlim i j) (Filter.eventually_atTop.2 ⟨1, fun k hk => hSeq k hk i j⟩)

theorem solution {ι : Type*} [Countable ι] [DecidableEq ι]
    (B A₀ A₁ A₂ : ι → ι → ℝ)
    (hP : IsStochasticC (qbdP B A₀ A₁ A₂))
    (hirr : IrreducibleC (qbdP B A₀ A₁ A₂)) :
    ((∀ i j, seriesInvE (matU (qbdP B A₀ A₁ A₂)) i j ≠ ⊤) ∧
      (∀ i j, matR (qbdP B A₀ A₁ A₂) i j ≠ ⊤) ∧
      matU (qbdP B A₀ A₁ A₂) = ennMat A₁ + matMulE (matR (qbdP B A₀ A₁ A₂)) (ennMat A₂) ∧
      matR (qbdP B A₀ A₁ A₂) = matMulE (ennMat A₀) (seriesInvE (matU (qbdP B A₀ A₁ A₂))) ∧
      ∀ X Z : ι → ι → ℝ, (∀ i j, 0 ≤ X i j) → (∀ i j, 0 ≤ Z i j) →
        (∀ i j, seriesInvE (ennMat X) i j ≠ ⊤) →
        ennMat X = ennMat A₁ + matMulE (ennMat Z) (ennMat A₂) →
        ennMat Z = matMulE (ennMat A₀) (seriesInvE (ennMat X)) →
        ∀ i j, matU (qbdP B A₀ A₁ A₂) i j ≤ ennMat X i j ∧
          matR (qbdP B A₀ A₁ A₂) i j ≤ ennMat Z i j) ∧
    (matU (qbdP B A₀ A₁ A₂) = ennMat A₁ +
        matMulE (matMulE (ennMat A₀) (seriesInvE (matU (qbdP B A₀ A₁ A₂)))) (ennMat A₂) ∧
      ∀ X : ι → ι → ℝ, (∀ i j, 0 ≤ X i j) →
        (∀ i j, seriesInvE (ennMat X) i j ≠ ⊤) →
        ennMat X = ennMat A₁ + matMulE (matMulE (ennMat A₀) (seriesInvE (ennMat X))) (ennMat A₂) →
        ∀ i j, matU (qbdP B A₀ A₁ A₂) i j ≤ ennMat X i j) ∧
    ((∀ i j, matR (qbdP B A₀ A₁ A₂) i j ≠ ⊤) ∧
      matR (qbdP B A₀ A₁ A₂) = ennMat A₀ + matMulE (matR (qbdP B A₀ A₁ A₂)) (ennMat A₁) +
        matMulE (matMulE (matR (qbdP B A₀ A₁ A₂)) (matR (qbdP B A₀ A₁ A₂))) (ennMat A₂) ∧
      ∀ Z : ι → ι → ℝ, (∀ i j, 0 ≤ Z i j) →
        ennMat Z = ennMat A₀ + matMulE (ennMat Z) (ennMat A₁) +
          matMulE (matMulE (ennMat Z) (ennMat Z)) (ennMat A₂) →
        ∀ i j, matR (qbdP B A₀ A₁ A₂) i j ≤ ennMat Z i j) := by
  set P := qbdP B A₀ A₁ A₂ with hPdef
  rcases UG_minimal B A₀ A₁ A₂ hP hirr with ⟨_hGfin, hSfin, hU, hG, _⟩
  rcases ur_path_factorization B A₀ A₁ A₂ hP hirr with ⟨hRfin, hR⟩
  have hU14 : matU P = ennMat A₁ +
      matMulE (matMulE (ennMat A₀) (seriesInvE (matU P))) (ennMat A₂) := by
    rw [urm_mm_assoc, ← hG]; exact hU
  have hU13 : matU P = ennMat A₁ + matMulE (matR P) (ennMat A₂) := by
    rw [hR]; exact hU14
  have hsuper := urm_U_le_super B A₀ A₁ A₂ hP hirr
  have hR16 : matR P = ennMat A₀ + matMulE (matR P) (ennMat A₁) +
      matMulE (matMulE (matR P) (matR P)) (ennMat A₂) := by
    calc matR P = matMulE (ennMat A₀) (seriesInvE (matU P)) := hR
      _ = matMulE (ennMat A₀) (matOneE + matMulE (seriesInvE (matU P)) (matU P)) := by
          rw [← urm_S_right]
      _ = ennMat A₀ + matMulE (matR P) (matU P) := by
          rw [urm_mm_add_right, urm_mm_one, ← urm_mm_assoc, ← hR]
      _ = _ := by
          rw [hU13, urm_mm_add_right, urm_mm_assoc, add_assoc]
  refine ⟨⟨hSfin, hRfin, hU13, hR, ?_⟩, ⟨hU14, ?_⟩, ⟨hRfin, hR16, ?_⟩⟩
  · intro X Z _ _ _ hX hZ
    have hUX : ∀ i j, matU P i j ≤ ennMat X i j := by
      apply hsuper
      intro i j
      rw [← urm_mm_assoc, ← hZ, ← hX]
    intro i j
    refine ⟨hUX i j, ?_⟩
    rw [hR, hZ]
    exact urm_mm_mono _ _ _ _ (fun _ _ => le_rfl) (urm_S_mono _ _ hUX) i j
  · intro X _ _ hX
    apply hsuper
    intro i j
    rw [← urm_mm_assoc, ← hX]
  · intro Z _ hZ
    set W : ι → ι → ℝ≥0∞ := ennMat A₁ + matMulE (ennMat Z) (ennMat A₂) with hW
    have hZW : ennMat Z = ennMat A₀ + matMulE (ennMat Z) W := by
      rw [hW, urm_mm_add_right, ← urm_mm_assoc, ← add_assoc]; exact hZ
    have hAS : ∀ i j, matMulE (ennMat A₀) (seriesInvE W) i j ≤ ennMat Z i j :=
      urm_super_S _ _ _ (fun i j => le_of_eq (congrFun (congrFun hZW.symm i) j))
    have hUW : ∀ i j, matU P i j ≤ W i j := by
      apply hsuper
      intro i j
      rw [← urm_mm_assoc, hW]
      simp only [Pi.add_apply]
      exact add_le_add le_rfl (urm_mm_mono _ _ _ _ hAS (fun _ _ => le_rfl) i j)
    intro i j
    rw [hR]
    exact le_trans (urm_mm_mono _ _ _ _ (fun _ _ => le_rfl) (urm_S_mono _ _ hUW) i j) (hAS i j)
