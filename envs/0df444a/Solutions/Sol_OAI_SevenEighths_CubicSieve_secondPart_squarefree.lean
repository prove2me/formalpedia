-- Prove2me | solution 1 for OAI.SevenEighths.CubicSieve.secondPart_squarefree
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T23:07:50.566276+00:00
-- url     : https://prove2.me/submissions/49559ff2-ce39-4bcf-bcb9-a3ffb25210e5

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
omit [Subsingleton Mˣ]

theorem solution (x : M) : Squarefree (secondPart x) := by
  classical
  unfold secondPart
  apply Finset.squarefree_prod_of_pairwise_isCoprime
  · intro p hp q hq hpq
    have hp' := Multiset.mem_toFinset.mp (Finset.mem_filter.mp hp).1
    have hq' := Multiset.mem_toFinset.mp (Finset.mem_filter.mp hq).1
    exact (prime_of_normalized_factor p hp').irreducible.isRelPrime_iff_not_dvd.mpr (fun hdvd =>
      hpq (normalizedFactors_eq_of_dvd x p hp' q hq' hdvd))
  · intro p hp
    have hp' := Multiset.mem_toFinset.mp (Finset.mem_filter.mp hp).1
    exact (prime_of_normalized_factor p hp').squarefree
