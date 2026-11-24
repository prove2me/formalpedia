-- Prove2me | solution 1 for GlobalTheory.HCA.exists_apOp_add_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T17:09:35.801599+00:00
-- url     : https://prove2.me/submissions/12d48041-fbc5-482a-b367-97b1b008575c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ZeroMemSolSet
import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllRegCheck
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsApOpAddSmul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ZetaZeros.D.EllReg GlobalTheory.HCA MeasureTheory
open scoped ContDiff BoundedContinuousFunction
open GlobalTheory GlobalTheory.HCA
namespace GlobalTheory.HCA
theorem _root_.solution : ∀ (d m m' : ℕ) (U : Set (E d)) (a a' : (n : ℕ) → (Fin n → Fin d) → E d → ℂ) (t : ℂ), m' ≤ m → (∀ n w, ContDiffOn ℝ ∞ (a n w) U) → (∀ n w, ContDiffOn ℝ ∞ (a' n w) U) → ∃ a'' : (n : ℕ) → (Fin n → Fin d) → E d → ℂ, (∀ n w, ContDiffOn ℝ ∞ (a'' n w) U) ∧ (∀ x ξ : E d, symb m a'' x ξ = symb m a x ξ + if m' = m then t * symb m' a' x ξ else 0) ∧ ∀ (u : E d → ℂ) (x : E d), apOp m a'' u x = apOp m a u x + t * apOp m' a' u x := by
  intro d m m' U a a' t hm ha ha'
  refine ⟨fun n w x => a n w x + if n ≤ m' then t * a' n w x else 0, ?_, ?_, ?_⟩
  · intro n w
    by_cases h : n ≤ m'
    · simp only [h, if_true]
      exact (ha n w).add (contDiffOn_const.mul (ha' n w))
    · simp only [h, if_false, add_zero]
      exact ha n w
  · intro x ξ
    by_cases h : m' = m
    · subst h
      simp only [symb, le_refl, if_true, add_mul, Finset.sum_add_distrib, Finset.mul_sum, mul_assoc]
    · have h' : ¬ m ≤ m' := fun h2 => h (le_antisymm hm h2)
      simp only [symb, h, h', if_false, add_zero]
  · intro u x
    simp only [apOp, add_mul, Finset.sum_add_distrib]
    congr 1
    rw [Finset.mul_sum]
    symm
    have hs : Finset.range (m' + 1) ⊆ Finset.range (m + 1) := by
      intro n hn
      simp only [Finset.mem_range] at hn ⊢
      omega
    rw [← Finset.sum_subset hs]
    · refine Finset.sum_congr rfl fun n hn => ?_
      have h : n ≤ m' := by simp only [Finset.mem_range] at hn; omega
      simp only [h, if_true, Finset.mul_sum, mul_assoc]
    · intro n _ hn
      have h : ¬ n ≤ m' := by simp only [Finset.mem_range] at hn; omega
      simp [h]
end GlobalTheory.HCA
