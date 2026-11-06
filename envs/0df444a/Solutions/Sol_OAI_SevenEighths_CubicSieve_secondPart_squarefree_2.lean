-- Prove2me | solution 2 for OAI.SevenEighths.CubicSieve.secondPart_squarefree
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T23:10:29.697903+00:00
-- url     : https://prove2.me/submissions/52036caf-4fa8-4b1f-9b24-0e646f879aec

import Mathlib.Algebra.Squarefree.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_Factorization
section
namespace OAI
namespace SevenEighths.CubicSieve
open scoped BigOperators Classical
open UniqueFactorizationMonoid
noncomputable section
variable {M : Type*} [CommMonoidWithZero M] [UniqueFactorizationMonoid M]
  [NormalizationMonoid M] [Subsingleton Mˣ]
omit [Subsingleton Mˣ] in
private theorem residual_squarefree (x : M) (r : ℕ) :
    Squarefree (∏ p ∈ (normalizedFactors x).toFinset.filter
      (fun p => (normalizedFactors x).count p % 3 = r), p) := by
  apply Finset.squarefree_prod_of_pairwise_isCoprime
  · intro p hp q hq hpq
    have hp' : p ∈ normalizedFactors x := Multiset.mem_toFinset.mp (Finset.mem_filter.mp hp).1
    have hq' : q ∈ normalizedFactors x := Multiset.mem_toFinset.mp (Finset.mem_filter.mp hq).1
    apply (irreducible_of_normalized_factor p hp').isRelPrime_iff_not_dvd.mpr
    intro hd
    exact hpq (normalizedFactors_eq_of_dvd x p hp' q hq' hd)
  · intro p hp
    exact (irreducible_of_normalized_factor p
      (Multiset.mem_toFinset.mp (Finset.mem_filter.mp hp).1)).squarefree
end
end SevenEighths.CubicSieve
end OAI
end

set_option autoImplicit false
open OAI
open OAI.SevenEighths OAI.SevenEighths.CubicSieve
open scoped BigOperators Classical
open UniqueFactorizationMonoid
noncomputable section
variable {M : Type*} [CommMonoidWithZero M] [UniqueFactorizationMonoid M]
  [NormalizationMonoid M] [Subsingleton Mˣ]
omit [Subsingleton Mˣ]
namespace OAI.SevenEighths.CubicSieve
theorem _root_.solution (x : M) : Squarefree (secondPart x) :=
  residual_squarefree x 2
end OAI.SevenEighths.CubicSieve
