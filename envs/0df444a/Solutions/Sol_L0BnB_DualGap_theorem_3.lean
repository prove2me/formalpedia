-- Prove2me | solution 1 for L0BnB.DualGap.theorem_3
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T03:56:08.222127+00:00
-- url     : https://prove2.me/submissions/2148ea4d-3cd3-471b-af3f-09e4053472b6

import Mathlib
import Definitions.Def_L0BnB_DualGap_Setup
import Definitions.Def_L0BnB_DualGap_Duals
import Theorems.Thm_L0BnB_DualGap_lemma_2
import Theorems.Thm_L0BnB_DualGap_ineq_53
import Theorems.Thm_L0BnB_DualGap_ineq_56
import Theorems.Thm_L0BnB_DualGap_ineq_57
import Theorems.Thm_L0BnB_DualGap_eq_28
import Theorems.Thm_L0BnB_DualGap_proposition_3

set_option autoImplicit false

namespace L0BnB.DualGap.Aux3

open L0BnB.DualGap

lemma v_nonneg {n p : ℕ} (X : Matrix (Fin n) (Fin p) ℝ) (lam0 lam2 M : ℝ) (hM : 0 < M)
    (α : Fin n → ℝ) (g : ℝ) (i : Fin p) : 0 ≤ v X lam0 lam2 M α g i := by
  unfold v
  have := le_max_right ((colInner X α i - g) ^ 2 / (4 * lam2) - lam0) 0
  have : 0 ≤ M * |g| := mul_nonneg hM.le (abs_nonneg g)
  linarith

lemma colInner_neg {n p : ℕ} (X : Matrix (Fin n) (Fin p) ℝ) (a : Fin n → ℝ) (i : Fin p) :
    colInner X (fun r => - a r) i = - colInner X a i := by
  unfold colInner
  simp [Finset.sum_neg_distrib]

end L0BnB.DualGap.Aux3

open L0BnB.DualGap L0BnB.DualGap.Aux3

theorem solution {n p : ℕ} (X : Matrix (Fin n) (Fin p) ℝ) (y : Fin n → ℝ)
    (lam0 lam2 M : ℝ) (hlam0 : 0 < lam0) (hlam2 : 0 < lam2) (hM : 0 < M)
    (hX : ∀ i, ∑ r, X r i ^ 2 = 1) (hy : ∑ r, y r ^ 2 = 1)
    (βs : Fin p → ℝ) (hβs : IsOptimal X y lam0 lam2 M βs)
    (βhat : Fin p → ℝ) (hbox : βhat ∈ L0BnB.Reduced.box p M) (hV : Vset X y lam0 lam2 M βhat = ∅)
    (γhat : Fin p → ℝ) (hγ : IsGammaHat X y lam0 lam2 M βhat γhat)
    (μhat : Fin p → ℝ) (hμ : IsMuHat X y lam0 lam2 M βhat μhat) :
    (Real.sqrt (lam0 / lam2) ≤ M →
      h1 X y lam0 lam2 M (L0BnB.Duality.alphaStar X y βs) (L0BnB.Duality.gammaStar X y lam2 M βs)
          - 2 * primalGap X βs βhat - (1 / 2) * primalGap X βs βhat ^ 2
          - ∑ i ∈ supp βhat,
              (cLemma2 lam2 M βs i * primalGap X βs βhat + (4 * lam2)⁻¹ * primalGap X βs βhat ^ 2)
        ≤ h1 X y lam0 lam2 M (alphaHat X y βhat) γhat) ∧
    (M < Real.sqrt (lam0 / lam2) →
      L0BnB.Duality.h2 y M (L0BnB.Duality.rhoStar X y βs) (L0BnB.Duality.muStar X y lam0 lam2 M βs)
          - primalGap X βs βhat * (2 + M * ((supp βhat).card : ℝ)) - primalGap X βs βhat ^ 2 / 2
        ≤ L0BnB.Duality.h2 y M (rhoHat X y βhat) μhat) := by
  classical
  set ε := primalGap X βs βhat
  constructor
  · intro hreg
    obtain ⟨hA, hB⟩ := L0BnB.DualGap.lemma_2 X y lam0 lam2 M hlam0 hlam2 hM hreg hX hy βs hβs βhat hbox hV γhat hγ
    have h53 := L0BnB.DualGap.ineq_53 X y lam0 lam2 M hlam0 hlam2 hM hy βs hβs βhat
    set E : Fin p → ℝ := fun i => cLemma2 lam2 M βs i * ε + (4 * lam2)⁻¹ * ε ^ 2
    have hpt : ∀ i, v X lam0 lam2 M (alphaHat X y βhat) (γhat i) i ≤
        (if βhat i ≠ 0 then E i else 0) +
          v X lam0 lam2 M (L0BnB.Duality.alphaStar X y βs) (L0BnB.Duality.gammaStar X y lam2 M βs i) i := by
      intro i
      by_cases hi : βhat i = 0
      · rw [hA i hi, if_neg (not_not.2 hi), zero_add]
        exact v_nonneg X lam0 lam2 M hM _ _ i
      · rw [if_pos hi]; exact hB i hi
    have hsum := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hpt i)
    rw [Finset.sum_add_distrib, ← Finset.sum_filter] at hsum
    have hsupp : supp βhat = Finset.univ.filter (fun i => βhat i ≠ 0) := by
      unfold supp; congr
    unfold h1
    rw [hsupp]
    linarith
  · intro hreg
    have h56 := L0BnB.DualGap.ineq_56 X y lam0 lam2 M hlam0 hlam2 hM hy βs hβs βhat μhat
    have hpt : ∀ i, |μhat i| ≤ (if βhat i ≠ 0 then ε else 0) +
        |L0BnB.Duality.muStar X y lam0 lam2 M βs i| := by
      intro i
      by_cases hi : βhat i = 0
      · rw [if_neg (not_not.2 hi), zero_add]
        have hc : |colInner X (resid X y βhat) i| ≤ cThr lam0 lam2 M := by
          by_contra hcon
          have : i ∈ Vset X y lam0 lam2 M βhat := by
            rw [L0BnB.DualGap.proposition_3 X y lam0 lam2 M hlam0 hlam2 hM hX βhat]
            simp only [Finset.mem_filter, Finset.mem_univ, true_and]
            exact ⟨hi, not_le.1 hcon⟩
          rw [hV] at this; simp at this
        have hthr : cThr lam0 lam2 M = lam0 / M + lam2 * M := by
          unfold cThr; rw [if_neg (not_le.2 hreg)]
        rw [hthr] at hc
        have e1 : colInner X (rhoHat X y βhat) i = - colInner X (resid X y βhat) i :=
          colInner_neg X _ i
        rw [L0BnB.DualGap.eq_28 X y lam0 lam2 M hlam0 hlam2 hM βhat μhat hμ i, e1, abs_neg,
          max_eq_right (by linarith)]
        simp
      · rw [if_pos hi]
        exact L0BnB.DualGap.ineq_57 X y lam0 lam2 M hlam0 hlam2 hM hreg hX βs hβs βhat μhat hμ i hi
    have hsum := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hpt i)
    rw [Finset.sum_add_distrib, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul] at hsum
    have hsupp : supp βhat = Finset.univ.filter (fun i => βhat i ≠ 0) := by
      unfold supp; congr
    rw [hsupp]
    have hMs := mul_le_mul_of_nonneg_left hsum hM.le
    unfold L0BnB.Duality.h2 at h56 ⊢
    have e2 : L0BnB.Duality.rhoStar X y βs = L0BnB.Duality.rhoStar X y βs := rfl
    nlinarith

