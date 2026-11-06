-- Prove2me | solution 2 for OAI.SevenEighths.CubicSieve.residual_parts_isRelPrime
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T23:10:52.078199+00:00
-- url     : https://prove2.me/submissions/2826eacc-0740-4c99-a1e1-7b2a1a9200d2

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
namespace OAI.SevenEighths.CubicSieve
theorem _root_.solution (x : M) : IsRelPrime (firstPart x) (secondPart x) := by
  unfold firstPart secondPart
  apply IsRelPrime.prod_left
  intro p hp
  apply IsRelPrime.prod_right
  intro q hq
  have hp' := Finset.mem_filter.mp hp
  have hq' := Finset.mem_filter.mp hq
  apply (irreducible_of_normalized_factor p (Multiset.mem_toFinset.mp hp'.1)).isRelPrime_iff_not_dvd.mpr
  intro hd
  have heq := normalizedFactors_eq_of_dvd x p (Multiset.mem_toFinset.mp hp'.1)
    q (Multiset.mem_toFinset.mp hq'.1) hd
  subst q
  omega
end OAI.SevenEighths.CubicSieve
