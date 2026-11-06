-- Prove2me | solution 2 for OAI.SevenEighths.CubicSieve.cubic_factorization
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-05T23:06:31.154422+00:00
-- url     : https://prove2.me/submissions/1dc2d860-2204-4ce7-bb24-2e30de222476

import Mathlib.Algebra.Squarefree.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_Factorization
set_option autoImplicit false
open OAI
open OAI.SevenEighths OAI.SevenEighths.CubicSieve
open scoped BigOperators Classical
open UniqueFactorizationMonoid
noncomputable section
variable {M : Type*} [CommMonoidWithZero M] [UniqueFactorizationMonoid M]
  [NormalizationMonoid M] [Subsingleton Mˣ]
theorem OA1Aux.pow_split {M : Type*} [CommMonoid M] (p : M) (c : ℕ) :
    p ^ c = (if c % 3 = 1 then p else 1) * (if c % 3 = 2 then p else 1) ^ 2 * (p ^ (c / 3)) ^ 3 := by
  have e : p ^ c = (p ^ (c / 3)) ^ 3 * p ^ (c % 3) := by
    rw [← pow_mul, ← pow_add]
    congr 1
    omega
  have : c % 3 = 0 ∨ c % 3 = 1 ∨ c % 3 = 2 := by omega
  rcases this with h | h | h
  · rw [if_neg (by omega), if_neg (by omega), e, h]
    simp
  · rw [if_pos h, if_neg (by omega), e, h]
    simp [mul_comm]
  · rw [if_neg (by omega), if_pos h, e, h]
    simp [mul_comm]

theorem solution (x : M) (hx : x ≠ 0) :
    x = firstPart x * secondPart x ^ 2 * cubePart x ^ 3 := by
  have hx' : (normalizedFactors x).prod = x := by
    obtain ⟨u, hu⟩ := prod_normalizedFactors hx
    rw [Subsingleton.elim u 1] at hu
    simpa using hu
  have hmain : x = ∏ p ∈ (normalizedFactors x).toFinset, p ^ (normalizedFactors x).count p := by
    conv_lhs => rw [← hx']
    exact Finset.prod_multiset_count _
  refine hmain.trans ?_
  unfold firstPart secondPart cubePart
  rw [Finset.prod_filter, Finset.prod_filter, ← Finset.prod_pow, ← Finset.prod_pow,
    ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl (fun p _ => OA1Aux.pow_split p _)
