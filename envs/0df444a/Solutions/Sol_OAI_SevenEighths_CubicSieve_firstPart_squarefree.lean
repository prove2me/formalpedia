-- Prove2me | solution 1 for OAI.SevenEighths.CubicSieve.firstPart_squarefree
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T23:06:34.422843+00:00
-- url     : https://prove2.me/submissions/179f9485-d876-4b45-8c73-23a2562ff586

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

theorem solution (x : M) : Squarefree (firstPart x) := by
  unfold firstPart
  apply Finset.squarefree_prod_of_pairwise_isCoprime
  · intro p hp q hq hpq
    have hp' : p ∈ normalizedFactors x :=
      Multiset.mem_toFinset.mp (Finset.mem_filter.mp hp).1
    have hq' : q ∈ normalizedFactors x :=
      Multiset.mem_toFinset.mp (Finset.mem_filter.mp hq).1
    apply (irreducible_of_normalized_factor p hp').isRelPrime_iff_not_dvd.mpr
    intro hd
    exact hpq (normalizedFactors_eq_of_dvd x p hp' q hq' hd)
  · intro p hp
    exact (irreducible_of_normalized_factor p
      (Multiset.mem_toFinset.mp (Finset.mem_filter.mp hp).1)).squarefree
