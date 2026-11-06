-- Prove2me | solution 1 for OAI.SevenEighths.CubicSieve.residual_parts_isRelPrime
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T23:10:02.785319+00:00
-- url     : https://prove2.me/submissions/8ed90ba7-3f9c-4ceb-9fef-064b999ed186

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
theorem solution (x : M) : IsRelPrime (firstPart x) (secondPart x) := by
  classical
  unfold firstPart secondPart
  apply IsRelPrime.prod_left
  intro p hp
  apply IsRelPrime.prod_right
  intro q hq
  have hp' : p ∈ normalizedFactors x :=
    Multiset.mem_toFinset.mp (Finset.mem_of_mem_filter p hp)
  have hq' : q ∈ normalizedFactors x :=
    Multiset.mem_toFinset.mp (Finset.mem_of_mem_filter q hq)
  apply (prime_of_normalized_factor p hp').irreducible.isRelPrime_iff_not_dvd.mpr
  intro hpq
  have h_assoc : Associated p q :=
    (prime_of_normalized_factor p hp').irreducible.associated_of_dvd
      (prime_of_normalized_factor q hq').irreducible hpq
  have hpq_eq : p = q := mem_normalizedFactors_eq_of_associated hp' hq' h_assoc
  have hp_count : (normalizedFactors x).count p % 3 = 1 := (Finset.mem_filter.mp hp).2
  have hq_count : (normalizedFactors x).count q % 3 = 2 := (Finset.mem_filter.mp hq).2
  subst q
  omega
