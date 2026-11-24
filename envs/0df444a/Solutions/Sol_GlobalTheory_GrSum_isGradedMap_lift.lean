-- Prove2me | solution 1 for GlobalTheory.GrSum.isGradedMap_lift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:22:32.490977+00:00
-- url     : https://prove2.me/submissions/73b1bca6-2e63-4212-ac20-f938b8410f02

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_XSmulMemWeightedHomogeneousSubmodule
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_WeightAddLeOfMemSupportDividedContraction
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsGradedMapLinearCombination

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
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
variable {N : Type*} [AddCommGroup N] [Module R N] [Module (MvPolynomial ι R) N]
  [IsScalarTower R (MvPolynomial ι R) N]
namespace GlobalTheory.GrSum
theorem _root_.solution (φ : ∀ n, A n →ₗ[R] N) (hφ) (𝒩 : ℤ → Submodule R N)
    (h : ∀ n a, φ n a ∈ 𝒩 n) : IsGradedMap (grading hx) 𝒩 (lift hx φ hφ) := by
  rintro n _ ⟨a, rfl⟩
  rw [lift_of]
  exact h n a
end GlobalTheory.GrSum
