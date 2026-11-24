-- Prove2me | solution 1 for GlobalTheory.GrSum.proj_grading
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:30:32.054364+00:00
-- url     : https://prove2.me/submissions/0d582db1-9be9-484f-a06c-5f0e40aab612

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_XSmulMemWeightedHomogeneousSubmodule
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_WeightAddLeOfMemSupportDividedContraction
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsGradedMapLinearCombination
import Theorems.Thm_GlobalTheory_GrSum_of_mem_grading
import Theorems.Thm_GlobalTheory_Wick_dividedContraction_one
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.Wick.dividedContraction_one



set_option autoImplicit false
open DirectSum MvPolynomial
noncomputable section
open GlobalTheory
open GradedHilbert
variable {ι : Type*} {R : Type*} [CommRing R]
  {A : ℤ → Type*} [∀ n, AddCommGroup (A n)] [∀ n, Module R (A n)]
  {B : ℤ → Type*} [∀ n, AddCommGroup (B n)] [∀ n, Module R (B n)]
open GlobalTheory.GrSum
variable {x : ι → ∀ n, A n →ₗ[R] A (n + 1)} (hx : OperatorsCommute x)
  {y : ι → ∀ n, B n →ₗ[R] B (n + 1)} (hy : OperatorsCommute y)
namespace GlobalTheory.GrSum
theorem _root_.solution (n : ℤ) (m : GrSum hx) :
    proj (grading hx) n m = of hx n (component hx n m) := by
  have : proj (grading hx) n = of hx n ∘ₗ component hx n := lhom_ext hx fun k a => by
    by_cases h : k = n
    · subst h
      simp [proj_of_mem _ (of_mem_grading hx k a)]
    · simp [proj_of_mem_ne _ (of_mem_grading hx k a) h, component_of_ne hx h]
  exact congr($this m)
end GlobalTheory.GrSum
