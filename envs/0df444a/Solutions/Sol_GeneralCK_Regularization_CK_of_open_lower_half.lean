-- Prove2me | solution 1 for GeneralCK.Regularization.CK_of_open_lower_half
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-24T22:22:38.929179+00:00
-- url     : https://prove2.me/submissions/6936ea09-3df0-493a-8c00-99cc99e8f55a

import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_GeneralCK_information
import Definitions.Def_GeneralCK_regularization
import Definitions.Def_GeneralCK_statement
import Theorems.Thm_GeneralCK_Information_mutualInformation_eq
import Theorems.Thm_GeneralCK_Information_mutualInformation_half
import Theorems.Thm_GeneralCK_noiseKernel_sum

open scoped BigOperators
namespace GeneralCK
open scoped BigOperators















theorem log_two_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)

@[simp] theorem H_zero : H 0 = 0 := by simp [H]
@[simp] theorem H_one : H 1 = 0 := by simp [H]
@[simp] theorem H_half : H (1 / 2) = 1 := by
  have h : Real.log 2 ≠ 0 := ne_of_gt log_two_pos
  simpa [H, one_div] using div_self h

theorem H_complement (p : ℝ) : H (1 - p) = H p := by simp [H]

theorem H_nonneg {p : ℝ} (h₀ : 0 ≤ p) (h₁ : p ≤ 1) : 0 ≤ H p :=
  div_nonneg (Real.binEntropy_nonneg h₀ h₁) log_two_pos.le

theorem H_le_one (p : ℝ) : H p ≤ 1 := by
  rw [H, div_le_one log_two_pos]
  exact Real.binEntropy_le_log_two



end GeneralCK

namespace GeneralCK
open scoped BigOperators

theorem noiseKernel_nonneg {n : ℕ} {p : ℝ} (h₀ : 0 ≤ p) (h₁ : p ≤ 1)
    (x y : Cube n) : 0 ≤ noiseKernel p x y := by
  unfold noiseKernel
  apply Finset.prod_nonneg
  intro i _
  split_ifs <;> linarith







end GeneralCK

namespace GeneralCK.Information
open scoped BigOperators









theorem kernel_symm {n : ℕ} (p : ℝ) (x y : Cube n) :
    noiseKernel p x y = noiseKernel p y x := by
  simp only [noiseKernel, eq_comm]

theorem kernel_column_sum {n : ℕ} (p : ℝ) (y : Cube n) :
    ∑ x, noiseKernel p x y = 1 := by
  simp_rw [kernel_symm p _ y]
  exact noiseKernel_sum p y





















theorem posterior_nonneg {n : ℕ} (f : Cube n → Bool) {p : ℝ}
    (h₀ : 0 ≤ p) (h₁ : p ≤ 1) (y : Cube n) : 0 ≤ posterior f p y := by
  apply Finset.sum_nonneg
  intro x _
  split_ifs
  · exact noiseKernel_nonneg h₀ h₁ x y
  · exact le_rfl

theorem posterior_le_one {n : ℕ} (f : Cube n → Bool) {p : ℝ}
    (h₀ : 0 ≤ p) (h₁ : p ≤ 1) (y : Cube n) : posterior f p y ≤ 1 := by
  rw [← kernel_column_sum p y]
  apply Finset.sum_le_sum
  intro x _
  split_ifs
  · exact le_rfl
  · exact noiseKernel_nonneg h₀ h₁ x y









end GeneralCK.Information

namespace GeneralCK.Regularization
open scoped BigOperators









theorem kernel_complement {n : ℕ} (p : ℝ) (x y : Cube n) :
    noiseKernel (1 - p) x y = noiseKernel p x (complementEquiv n y) := by
  apply Finset.prod_congr rfl
  intro i _
  change (if x i = y i then 1 - (1 - p) else 1 - p) =
    (if x i = !(y i) then 1 - p else p)
  cases x i <;> cases y i <;> simp

theorem posterior_complement {n : ℕ} (f : Cube n → Bool) (p : ℝ) (y : Cube n) :
    Information.posterior f (1 - p) y =
      Information.posterior f p (complementEquiv n y) := by
  simp only [Information.posterior, kernel_complement]

theorem mutualInformation_complement {n : ℕ} (f : Cube n → Bool) (p : ℝ) :
    mutualInformation f (1 - p) = mutualInformation f p := by
  simp only [Information.mutualInformation_eq, posterior_complement]
  rw [Equiv.sum_comp (complementEquiv n) (fun y => H (Information.posterior f p y))]

theorem mutualInformation_le_one {n : ℕ} (f : Cube n → Bool) {p : ℝ}
    (hp : 0 ≤ p) (hp' : p ≤ 1) : mutualInformation f p ≤ 1 := by
  rw [Information.mutualInformation_eq]
  have hsum : 0 ≤ ∑ y, H (Information.posterior f p y) := by
    apply Finset.sum_nonneg
    intro y _
    exact H_nonneg (Information.posterior_nonneg f hp hp' y)
      (Information.posterior_le_one f hp hp' y)
  have hw : 0 ≤ Information.cubeWeight n := by unfold Information.cubeWeight; positivity
  have := mul_nonneg hw hsum
  have := H_le_one (Information.meanIndicator f)
  linarith

theorem CK_zero {n : ℕ} (f : Cube n → Bool) : mutualInformation f 0 ≤ 1 - H 0 := by
  simpa using mutualInformation_le_one f (p := 0) (by norm_num) (by norm_num)

theorem CK_one {n : ℕ} (f : Cube n → Bool) : mutualInformation f 1 ≤ 1 - H 1 := by
  simpa using mutualInformation_le_one f (p := 1) (by norm_num) (by norm_num)



end GeneralCK.Regularization
namespace GeneralCK.Regularization
end GeneralCK.Regularization

open GeneralCK GeneralCK.Regularization in
open scoped BigOperators in
theorem solution
    (h : ∀ (n : ℕ) (f : Cube n → Bool) (p : ℝ),
      0 < p → p < 1 / 2 → mutualInformation f p ≤ 1 - H p) :
    GeneralCourtadeKumar := by
  intro n f p hp hp'
  by_cases hzero : p = 0
  · subst p; exact CK_zero f
  by_cases hone : p = 1
  · subst p; exact CK_one f
  by_cases hhalf : p = 1 / 2
  · subst p
    rw [Information.mutualInformation_half, H_half]
    norm_num
  by_cases hlower : p < 1 / 2
  · exact h n f p (lt_of_le_of_ne hp (Ne.symm hzero)) hlower
  · have hpstrict : p < 1 := lt_of_le_of_ne hp' hone
    have hphalf : 1 / 2 < p := lt_of_le_of_ne (le_of_not_gt hlower) (Ne.symm hhalf)
    have hc := h n f (1 - p) (by linarith) (by linarith)
    simpa only [mutualInformation_complement, H_complement] using hc
