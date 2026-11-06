-- Prove2me | solution 1 for OAI.SevenEighths.CubicSieve.extraction_injective_on_nonzero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T23:10:52.782975+00:00
-- url     : https://prove2.me/submissions/706ce806-4c2b-4a38-82f2-3847243eba0c

import Mathlib.Algebra.Squarefree.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_Factorization
import Theorems.Thm_OAI_SevenEighths_CubicSieve_cubic_factorization

set_option autoImplicit false
open OAI
open OAI.SevenEighths OAI.SevenEighths.CubicSieve
open scoped BigOperators Classical
open UniqueFactorizationMonoid
noncomputable section
variable {M : Type*} [CommMonoidWithZero M] [UniqueFactorizationMonoid M]
  [NormalizationMonoid M] [Subsingleton Mˣ]
namespace OAI.SevenEighths.CubicSieve
theorem _root_.solution :
    Set.InjOn (fun x : M => (firstPart x, secondPart x, cubePart x)) {x | x ≠ 0} := by
  intro x hx y hy h
  have h1 := congrArg (fun t : M × M × M => t.1) h
  have h2 := congrArg (fun t : M × M × M => t.2.1) h
  have h3 := congrArg (fun t : M × M × M => t.2.2) h
  dsimp only at h1 h2 h3
  rw [cubic_factorization x hx, cubic_factorization y hy, h1, h2, h3]
end OAI.SevenEighths.CubicSieve
